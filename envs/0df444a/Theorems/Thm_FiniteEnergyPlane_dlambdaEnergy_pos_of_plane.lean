-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_pos_of_plane
-- name    : FiniteEnergyPlane.dlambdaEnergy_pos_of_plane
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:24:51.466385+00:00
-- url     : https://prove2.me/theorems/3deeb338-4a09-4794-8343-4bd457061c6d
-- title:
--   Nonconstant finite-energy planes have positive $d\lambda$-energy
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a nonconstant finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}$. Then $\int_{\mathbb{C}}u^*d\lambda_0>0$.
--
--   **Formalization Note** The $d\lambda$-energy is a lower integral in `ℝ≥0∞`; the conclusion is `0 < dlambdaEnergy H Set.univ u`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Corollary 2.19, p. 12; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Corollary 29, p. 536

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer 1993, Corollary 29 (p. 536); Hryniewicz 2014, Corollary 2.19. A nonconstant
finite-energy `J̃`-holomorphic plane has positive `dλ`-energy. -/
theorem dlambdaEnergy_pos_of_plane {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    0 < dlambdaEnergy H Set.univ u := by
  sorry

end FiniteEnergyPlane
