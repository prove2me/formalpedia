-- Prove2me | Theorems.Thm_FiniteEnergyPlane_not_forall_exists_aCoord_le_of_gradNorm_bounded
-- name    : FiniteEnergyPlane.not_forall_exists_aCoord_le_of_gradNorm_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:06:13.158468+00:00
-- url     : https://prove2.me/theorems/64c566e4-db9b-4dd4-b780-f3750f0760aa
-- title:
--   Fast planes with locally bounded gradients have $\inf a$ not tending to $-\infty$
-- statement:
--   Let $P=(x,T)$ be a periodic Reeb orbit on a strictly star-shaped level $S\subset\mathbb{R}^4$, let $0<\gamma$ be smaller than every period at most $T$, and let $K\subset\mathbb{R}^4\setminus\{0\}$ be compact. Let $u_k$ be a sequence in the set $\Theta(K,P)$ of fast finite-energy planes asymptotic to $P$ at $\infty$ with $u_k(0)\in K$ and $d\lambda$-energy $\gamma$ outside the closed unit disk. If the gradients of $u_k$ are uniformly bounded on every compact subset of $\mathbb{C}$, then $\inf_{\mathbb{C}} a_k$ does not tend to $-\infty$, where $a_k$ is the symplectization coordinate of $u_k$.
--
--   In the compactness theory of fast planes this rules out the loss of a lower bound on $a_k$ when no gradient blow-up occurs.
--
--   **Formalization Note** $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$ is `V 1 \ {0}`, with $a$ = `aCoord H` and $\mathrm{pr}$ = `proj H`; $\Theta$ = `fastPlaneSet H J P K γ`. The conclusion is the negation of `∀ M, ∀ᶠ k, ∃ z, a_k z ≤ M`; the gradient is `gradNorm H (u k)`.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` be a periodic Reeb orbit on `S ⊂ ℝ⁴`, `0 < γ` smaller than every period at most `P.T`, and
`K ⊂ V 1 \ {0}` compact. If a sequence `uₖ` in `fastPlaneSet H J P K γ` has gradients uniformly
bounded on every compact subset of `ℂ`, then `inf aₖ` does not tend to `-∞` (`aₖ = aCoord H ∘ uₖ`). -/
theorem not_forall_exists_aCoord_le_of_gradNorm_bounded (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (hgrad : ∀ Kc : Set ℂ, IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, gradNorm H (u k) z ≤ M) :
    ¬ ∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, aCoord H (u k z) ≤ M := by
  sorry

end FiniteEnergyPlane
