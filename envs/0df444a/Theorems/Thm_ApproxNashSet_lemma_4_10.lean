-- Prove2me | Theorems.Thm_ApproxNashSet_lemma_4_10
-- name    : ApproxNashSet.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:04.851039+00:00
-- url     : https://prove2.me/theorems/56964fd9-8c8f-4e56-8386-3b2888b047ce
-- title:
--   Lemma 4.10 — $\operatorname{argMin}\subseteq\bigcup_j\bar X^j_i\subseteq\varepsilon_1\operatorname{argMin}$ for problem (3)
-- statement:
--   Let $\mathbb X=\operatorname{conv}V$ for a nonempty finite set $V$ (Assumption 4.2, which gives Assumption 4.1.1), let every $f_i$ be convex (Assumption 4.1.2), let $\varepsilon_1,\varepsilon_2>0$, and consider a run of Algorithm 4.8 with step-2 sets $F^1,\dots,F^{k_i}$ and convex projections $\bar X^j_i=\{x\in\mathbb X:\exists y\in F^j,\ (x_{-i},-x_{-i},f_i(x))\le y\}$. Then for every player $i$,
--   $$\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\}\subseteq\bigcup_{j=1}^{k_i}\bar X^j_i\subseteq\varepsilon_1\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\},$$
--   where $\varepsilon_1\operatorname{argMin}$ is ε₁-Pareto optimality in direction $\bar c_i=(0,\dots,0,1)$.
--
--   The exact convex projections thus sandwich the Pareto set of (3) between itself and its ε₁-relaxation; Lemma 4.11 then accounts for the error of approximating them.
--
--   **Formalization Note** The run abstracts the external subroutines by their guarantees (definition `Run`).
--
--   Differences from the source:
--   - reading: the set computed by Algorithm 4.8 → any run R : Run n f X V ε₁ ε₂, i.e. any subroutine outputs X̄ᵢ, F^j, X̂ʲᵢ meeting the guarantees (10) right half, (12), X̄ᵢ ⊆ X, the cover of the minimal elements by efficient sets, X̂ʲᵢ ⊆ X and (15); P^In_i, X̄ʲᵢ (14), 𝒳ᵢ and 𝒳 are defined from them; reason: steps 1–3 call external algorithms ([14], [1, 25, 24], [11]) that the paper specifies only by these guarantees, and the proof uses nothing else
--   - generalization: step 2: the maximal efficient faces F¹, …, F^{kᵢ} of (13) → any finite family of sets of minimal elements of P^In_i whose union contains every minimal element; reason: p.9 states that the maximal efficient faces form such a family, and the proof uses nothing else
--   - generalization: (10): P^In_i ⊆ Pᵢ ⊆ P^In_i − ε₁{c̄ᵢ} → only Pᵢ ⊆ P^In_i − ε₁{c̄ᵢ}; reason: P^In_i ⊆ Pᵢ follows from X̄ᵢ ⊆ X and the convexity of the fᵢ
--   - generalization: N ≥ 2 players → any finite player type; reason: the statement concerns one player i and uses nothing about the others' number; N ≥ 2 is a special case
--   - encoding: Assumption 4.1.1 (X convex and compact) and Assumption 4.2 (X = conv{x̄¹, …, x̄ᵏ} a nonempty polytope) → X = convexHull ℝ V for a nonempty Finset V; reason: a nonempty polytope given as a convex hull of finitely many points is convex and compact, so 4.1.1 is implied (not restated)
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, Lemma 4.10, p.11

import Mathlib
import Definitions.Def_ApproxNashSet_Model
import Definitions.Def_ApproxNashSet_Algorithm

open scoped Pointwise

namespace ApproxNashSet

/-- **Lemma 4.10 — the exact convex projections sandwich the Pareto set.**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, Lemma 4.10, p.11: "Let Assumptions 4.1 and 4.2 be
satisfied. For any i = 1, ..., N it holds argMin{(x−i, −x−i, fi(x)) | x ∈ X} ⊆ ⋃_{j=1}^{ki} X̄j_i ⊆
ε1 argMin{(x−i, −x−i, fi(x)) | x ∈ X}."

Hypotheses: Assumption 4.2 (`X = conv V`, `V` nonempty and finite; this implies Assumption 4.1.1,
`X` convex and compact), Assumption 4.1.2 (every `fᵢ` convex), approximation levels `ε₁, ε₂ > 0`,
and a run `R` of Algorithm 4.8. `X̄ʲᵢ` is the convex projection (14) of the `j`-th set of step 2.

**Formalization Note.** The run abstracts the external subroutines of steps 1–3 by their stated
guarantees (see `Run`). -/
theorem lemma_4_10 {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (X : Set (Joint n)) (V : Finset (Joint n))
    (hV : V.Nonempty) (hX : X = convexHull ℝ (↑V : Set (Joint n)))
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (R : Run n f X V ε₁ ε₂) (i : ι) :
    argMin (g n f i) X ⊆ ⋃ j, convProj (g n f i) X (R.F i j) ∧
      (⋃ j, convProj (g n f i) X (R.F i j)) ⊆ epsArgMin (g n f i) X (cbar n i) ε₁ := by sorry

end ApproxNashSet
