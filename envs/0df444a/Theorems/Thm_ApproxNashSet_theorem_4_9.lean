-- Prove2me | Theorems.Thm_ApproxNashSet_theorem_4_9
-- name    : ApproxNashSet.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:11.034203+00:00
-- url     : https://prove2.me/theorems/af2edc24-9cfa-49a3-acc4-7d68f1ad78ea
-- title:
--   Theorem 4.9 (corrected: $\epsilon=\varepsilon_1+(2+\kappa)L\varepsilon_2$, $\kappa$ a slice modulus) — $\mathrm{NE}(f,\mathbb X)\subseteq\mathcal X\subseteq\epsilon\,\mathrm{NE}(f,\mathbb X)$
-- statement:
--   Consider a game with finitely many players on a shared polytope $\mathbb X=\operatorname{conv}V$, $V$ a nonempty finite set (Assumption 4.2, which gives Assumption 4.1.1), with convex costs $f_i$ (Assumption 4.1.2) and a common L1-Lipschitz constant $L\ge0$ on $\mathbb X$: $|f_i(x)-f_i(y)|\le L\|x-y\|_1$. Let $\varepsilon_1,\varepsilon_2>0$ and let $\mathcal X$ be the output of a run of Algorithm 4.8,
--   $$\mathcal X=\bigcap_{i=1}^N\ \bigcup_{j=1}^{k_i}(\operatorname{conv}\hat X^j_i+B_{\varepsilon_2})\cap\mathbb X .$$
--   Then
--
--   1. every Nash equilibrium is in $\mathcal X$: $\mathrm{NE}(f,\mathbb X)\subseteq\mathcal X$;
--   2. for every $\kappa\ge0$ that is a slice modulus of $\mathbb X$,
--   $$\mathcal X\subseteq(\varepsilon_1+(2+\kappa)L\varepsilon_2)\,\mathrm{NE}(f,\mathbb X).$$
--
--   Here $\kappa$ is a slice modulus if for every player $i$ and all $x,z\in\mathbb X$ there is $x'\in\mathbb X$ with $x'_{-i}=z_{-i}$ and $\|x'_i-x_i\|_1\le\kappa\sum_{j\ne i}\|x_j-z_j\|_1$. For a product set such as a box, $\kappa=0$ works and the theorem is the printed sandwich $\mathrm{NE}(f,\mathbb X)\subseteq\mathcal X\subseteq(\varepsilon_1+2L\varepsilon_2)\mathrm{NE}(f,\mathbb X)$.
--
--   The computed set is finitely generated, contains every equilibrium, and contains only approximate equilibria, which is the main result of the paper.
--
--   **Formalization Note** The Nash equilibrium set is the published `NashVecOpt.SharedConstraint.NE`; ε-NE is the universal form of Definition 2.2; the run abstracts the external subroutines of steps 1–3 by their guarantees.
--
--   Differences from the source:
--   - correction: 𝒳 ⊆ (ε₁ + 2Lε₂) NE(f, X) (Lemma 4.11: 𝒳ᵢ ⊆ (ε₁ + 2Lε₂) argMin) → for every κ ≥ 0 that is a slice modulus of X: ⊆ with ε₁ + (2 + κ)Lε₂; reason: the printed inclusion is false: X = conv{(0,0),(0,1/10),(1,1/10)}, f₁ = −x₁, f₂ = 0, L = 1, ε₁ = ε₂ = 1/100 satisfy every assumption, x̄ = (0, 1/100) lies in 𝒳 for the run with X̄ᵢ the three vertices and, for player 1, X̂ = the two ends (0,0), (1,1/10) of the efficient edge, and player 1 gains 1/10 > 3/100 by moving to (1/10, 1/100) ∈ X; the proof of Lemma 4.11 applies ε₁-Pareto optimality of x* at (xᵢ, x*₋ᵢ), which need not lie in X. At κ = 0 (X a product of its projections, e.g. a box) the constant is the printed ε₁ + 2Lε₂
--   - reading: the set computed by Algorithm 4.8 → any run R : Run n f X V ε₁ ε₂, i.e. any subroutine outputs X̄ᵢ, F^j, X̂ʲᵢ meeting the guarantees (10) right half, (12), X̄ᵢ ⊆ X, the cover of the minimal elements by efficient sets, X̂ʲᵢ ⊆ X and (15); P^In_i, X̄ʲᵢ (14), 𝒳ᵢ and 𝒳 are defined from them; reason: steps 1–3 call external algorithms ([14], [1, 25, 24], [11]) that the paper specifies only by these guarantees, and the proof uses nothing else
--   - generalization: step 2: the maximal efficient faces F¹, …, F^{kᵢ} of (13) → any finite family of sets of minimal elements of P^In_i whose union contains every minimal element; reason: p.9 states that the maximal efficient faces form such a family, and the proof uses nothing else
--   - generalization: (10): P^In_i ⊆ Pᵢ ⊆ P^In_i − ε₁{c̄ᵢ} → only Pᵢ ⊆ P^In_i − ε₁{c̄ᵢ}; reason: P^In_i ⊆ Pᵢ follows from X̄ᵢ ⊆ X and the convexity of the fᵢ
--   - generalization: L > 0 the largest of the Lipschitz constants of the fᵢ on X (L1 norm) → any L ≥ 0 with |fᵢ(x) − fᵢ(y)| ≤ L‖x − y‖₁ for all i and x, y ∈ X; reason: the paper's L is such a constant
--   - generalization: N ≥ 2 players → any nonempty finite player type; reason: no step uses N ≥ 2; nonemptiness is kept because an empty intersection over players would be the whole space
--   - encoding: Assumption 4.1.1 (X convex and compact) and Assumption 4.2 (X = conv{x̄¹, …, x̄ᵏ} a nonempty polytope) → X = convexHull ℝ V for a nonempty Finset V; reason: a nonempty polytope given as a convex hull of finitely many points is convex and compact, so 4.1.1 is implied (not restated)
--   - encoding: ε NE(f, X) := {x* ∈ X | ∀i : fi(x*) ≤ inf{fi(xi, x*−i) | (xi, x*−i) ∈ X} + ε} → the universal form of Definition 2.2's first sentence; reason: the two agree (the infimum is over a set containing fᵢ(x*)); a real sInf of a set unbounded below is 0 in Lean
--   - encoding: ‖·‖ the L1 norm on ∏ⱼ Xⱼ and B_ε₂ its closed ball around 0 → l1 x = ∑ⱼ ∑ₖ |xⱼₖ| written out and ballL1 n ε₂ = {b | l1 b ≤ ε₂}; reason: Mathlib's norm on function types is the sup norm; the same norm as the page's
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, Theorem 4.9, (16), p.11 (proof p.12)

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Game
import Definitions.Def_ApproxNashSet_Model
import Definitions.Def_ApproxNashSet_Algorithm

open scoped Pointwise

namespace ApproxNashSet

/-- **Theorem 4.9 (corrected) — Algorithm 4.8's output contains every Nash equilibrium and
consists of approximate Nash equilibria.**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, Theorem 4.9, (16), p.11 (proof p.12): "Let Assumptions
4.1 and 4.2 be satisfied. Let X ⊆ R^{Σ ni} be the set computed by Algorithm 4.8 and let
ǫ = ε1 + 2Lε2. Then it holds NE(f, X) ⊆ X ⊆ ǫ NE(f, X)."

Hypotheses: a nonempty finite set of players `ι`; Assumption 4.2 (`X = conv V`, `V` a nonempty
finite set; this implies Assumption 4.1.1, `X` convex and compact); Assumption 4.1.2 (every `fᵢ`
convex on `∏ⱼ ℝ^{nⱼ}`); a common L1-Lipschitz constant `L ≥ 0` of the `fᵢ` on `X` (p.5);
approximation levels `ε₁, ε₂ > 0`; and a run `R` of Algorithm 4.8 with output
`𝒳 = ⋂ᵢ ⋃ⱼ (conv X̂ʲᵢ + B_{ε₂}) ∩ X`. Conclusion:

1. `NE(f, X) ⊆ 𝒳` (as printed);
2. for every `κ ≥ 0` that is a slice modulus of `X`, `𝒳 ⊆ (ε₁ + (2 + κ) L ε₂) NE(f, X)`.

**Formalization Note.** The printed right inclusion with `ε = ε₁ + 2Lε₂` is false for
non-product polytopes. Counterexample: `X = conv{(0,0), (0,1/10), (1,1/10)} ⊆ ℝ × ℝ`,
`f₁(x) = −x₁`, `f₂ = 0`, `L = 1`, `ε₁ = ε₂ = 1/100`: `x̄ = (0, 1/100)` lies in `𝒳` for the run
with `Xbar i` the three vertices and `Xhat` for player 1 the two ends `(0,0), (1,1/10)` of the
efficient edge, but player 1 gains `1/10 > 3/100` by moving to `(1/10, 1/100) ∈ X`. At `κ = 0`
(`X` a product of
its projections, e.g. a box) the corrected constant is the printed `ε₁ + 2Lε₂`. `NE` is the
published `NashVecOpt.SharedConstraint.NE` (Definition 2.1); `ε NE` is the universal form of
Definition 2.2; `‖·‖` is the L1 norm `∑ⱼ ∑ₖ |xⱼₖ|`; the run abstracts the external subroutines of
steps 1–3 by their stated guarantees (see `Run`). -/
theorem theorem_4_9 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (X : Set (Joint n)) (V : Finset (Joint n))
    (hV : V.Nonempty) (hX : X = convexHull ℝ (↑V : Set (Joint n)))
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (L : ℝ) (hL : 0 ≤ L) (hLip : IsL1Lipschitz f X L)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (R : Run n f X V ε₁ ε₂) :
    NashVecOpt.SharedConstraint.NE f X ⊆ R.calX ∧
      ∀ κ : ℝ, 0 ≤ κ → IsSliceModulus X κ →
        R.calX ⊆ epsNE f X (ε₁ + (2 + κ) * L * ε₂) := by sorry

end ApproxNashSet
