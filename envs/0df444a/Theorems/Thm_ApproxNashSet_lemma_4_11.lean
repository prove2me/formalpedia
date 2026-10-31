-- Prove2me | Theorems.Thm_ApproxNashSet_lemma_4_11
-- name    : ApproxNashSet.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:15.184977+00:00
-- url     : https://prove2.me/theorems/0faf6fcf-aa1e-4875-ada4-57af38533b8a
-- title:
--   Lemma 4.11 (corrected: $\epsilon=\varepsilon_1+(2+\kappa)L\varepsilon_2$, $\kappa$ a slice modulus) — $\operatorname{argMin}\subseteq\mathcal X_i\subseteq\epsilon\operatorname{argMin}$
-- statement:
--   Let $\mathbb X=\operatorname{conv}V$ for a nonempty finite set $V$, let every $f_i$ be convex, let $L\ge0$ satisfy $|f_i(x)-f_i(y)|\le L\|x-y\|_1$ for all $i$ and $x,y\in\mathbb X$ (L1 norm), let $\varepsilon_1,\varepsilon_2>0$, and consider a run of Algorithm 4.8 with per-player output
--   $$\mathcal X_i=\bigcup_{j=1}^{k_i}(\operatorname{conv}\hat X^j_i+B_{\varepsilon_2})\cap\mathbb X .$$
--   Then for every player $i$:
--
--   1. $\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\}\subseteq\mathcal X_i$;
--   2. for every $\kappa\ge0$ that is a slice modulus of $\mathbb X$ for player $i$,
--   $$\mathcal X_i\subseteq(\varepsilon_1+(2+\kappa)L\varepsilon_2)\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\}.$$
--
--   A slice modulus $\kappa$ for player $i$ means: for all $x,z\in\mathbb X$ there is $x'\in\mathbb X$ with $x'_{-i}=z_{-i}$ and $\|x'_i-x_i\|_1\le\kappa\sum_{j\ne i}\|x_j-z_j\|_1$. When $\mathbb X$ is a product of its projections (for example a box), $\kappa=0$ is a slice modulus and the constant is the printed $\varepsilon_1+2L\varepsilon_2$.
--
--   Differences from the source:
--   - correction: 𝒳 ⊆ (ε₁ + 2Lε₂) NE(f, X) (Lemma 4.11: 𝒳ᵢ ⊆ (ε₁ + 2Lε₂) argMin) → for every κ ≥ 0 that is a slice modulus of X for player i: ⊆ with ε₁ + (2 + κ)Lε₂; reason: the printed inclusion is false: X = conv{(0,0),(0,1/10),(1,1/10)}, f₁ = −x₁, f₂ = 0, L = 1, ε₁ = ε₂ = 1/100 satisfy every assumption, x̄ = (0, 1/100) lies in 𝒳 for the run with X̄ᵢ the three vertices and, for player 1, X̂ = the two ends (0,0), (1,1/10) of the efficient edge, and player 1 gains 1/10 > 3/100 by moving to (1/10, 1/100) ∈ X; the proof of Lemma 4.11 applies ε₁-Pareto optimality of x* at (xᵢ, x*₋ᵢ), which need not lie in X. At κ = 0 (X a product of its projections, e.g. a box) the constant is the printed ε₁ + 2Lε₂
--   - reading: the set computed by Algorithm 4.8 → any run R : Run n f X V ε₁ ε₂, i.e. any subroutine outputs X̄ᵢ, F^j, X̂ʲᵢ meeting the guarantees (10) right half, (12), X̄ᵢ ⊆ X, the cover of the minimal elements by efficient sets, X̂ʲᵢ ⊆ X and (15); P^In_i, X̄ʲᵢ (14), 𝒳ᵢ and 𝒳 are defined from them; reason: steps 1–3 call external algorithms ([14], [1, 25, 24], [11]) that the paper specifies only by these guarantees, and the proof uses nothing else
--   - generalization: step 2: the maximal efficient faces F¹, …, F^{kᵢ} of (13) → any finite family of sets of minimal elements of P^In_i whose union contains every minimal element; reason: p.9 states that the maximal efficient faces form such a family, and the proof uses nothing else
--   - generalization: (10): P^In_i ⊆ Pᵢ ⊆ P^In_i − ε₁{c̄ᵢ} → only Pᵢ ⊆ P^In_i − ε₁{c̄ᵢ}; reason: P^In_i ⊆ Pᵢ follows from X̄ᵢ ⊆ X and the convexity of the fᵢ
--   - generalization: L > 0 the largest of the Lipschitz constants of the fᵢ on X (L1 norm) → any L ≥ 0 with |fᵢ(x) − fᵢ(y)| ≤ L‖x − y‖₁ for all i and x, y ∈ X; reason: the paper's L is such a constant
--   - generalization: N ≥ 2 players → any finite player type; reason: the statement concerns one player i and uses nothing about the others' number; N ≥ 2 is a special case
--   - encoding: Assumption 4.1.1 (X convex and compact) and Assumption 4.2 (X = conv{x̄¹, …, x̄ᵏ} a nonempty polytope) → X = convexHull ℝ V for a nonempty Finset V; reason: a nonempty polytope given as a convex hull of finitely many points is convex and compact, so 4.1.1 is implied (not restated)
--   - encoding: ‖·‖ the L1 norm on ∏ⱼ Xⱼ and B_ε₂ its closed ball around 0 → l1 x = ∑ⱼ ∑ₖ |xⱼₖ| written out and ballL1 n ε₂ = {b | l1 b ≤ ε₂}; reason: Mathlib's norm on function types is the sup norm; the same norm as the page's
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, Lemma 4.11, p.11 (proof p.12)

import Mathlib
import Definitions.Def_ApproxNashSet_Model
import Definitions.Def_ApproxNashSet_Algorithm

open scoped Pointwise

namespace ApproxNashSet

/-- **Lemma 4.11 (corrected) — the computed set `𝒳ᵢ` sandwiches the Pareto set.**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, Lemma 4.11, p.11 (proof p.12): "Let Assumptions 4.1 and
4.2 be satisfied. Let ǫ = ε1 + 2Lε2. For any i = 1, ..., N it holds
argMin{(x−i, −x−i, fi(x)) | x ∈ X} ⊆ Xi ⊆ ǫ argMin{(x−i, −x−i, fi(x)) | x ∈ X}."

Hypotheses: Assumption 4.2 (`X = conv V`, `V` nonempty and finite), Assumption 4.1.2 (every `fᵢ`
convex), a common L1-Lipschitz constant `L ≥ 0` of the `fᵢ` on `X` (p.5), `ε₁, ε₂ > 0`, and a run
`R` of Algorithm 4.8 with per-player output `𝒳ᵢ = ⋃ⱼ (conv X̂ʲᵢ + B_{ε₂}) ∩ X`. Conclusion:

1. `argMin{gᵢ | X} ⊆ 𝒳ᵢ` (as printed);
2. for every `κ ≥ 0` that is a slice modulus of `X` for player `i`,
   `𝒳ᵢ ⊆ (ε₁ + (2 + κ) L ε₂) argMin{gᵢ | X}`.

**Formalization Note.** The printed right inclusion with `ε₁ + 2Lε₂` is false for non-product
polytopes (the proof applies ε₁-Pareto optimality of `x*` at `(xᵢ, x*₋ᵢ)`, which need not lie in
`X`). Counterexample: `X = conv{(0,0), (0,1/10), (1,1/10)}`, `f₁ = −x₁`, `f₂ = 0`, `L = 1`,
`ε₁ = ε₂ = 1/100`, `i = 1`, and `x̄ = (0, 1/100)`. At `κ = 0` (`(xᵢ, z₋ᵢ) ∈ X` for all `x, z ∈ X`,
e.g. boxes) the corrected constant is the printed one. -/
theorem lemma_4_11 {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (X : Set (Joint n)) (V : Finset (Joint n))
    (hV : V.Nonempty) (hX : X = convexHull ℝ (↑V : Set (Joint n)))
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (L : ℝ) (hL : 0 ≤ L) (hLip : IsL1Lipschitz f X L)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (R : Run n f X V ε₁ ε₂) (i : ι) :
    argMin (g n f i) X ⊆ R.calXi i ∧
      ∀ κ : ℝ, 0 ≤ κ → IsSliceModulusAt X κ i →
        R.calXi i ⊆ epsArgMin (g n f i) X (cbar n i) (ε₁ + (2 + κ) * L * ε₂) := by sorry

end ApproxNashSet
