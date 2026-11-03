-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_xiCoordC_smul_xiFrame
-- name    : FiniteEnergyPlane.eq_xiCoordC_smul_xiFrame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T15:22:50.199538+00:00
-- url     : https://prove2.me/theorems/a949d9bb-db11-4300-9129-63625bea5f97
-- title:
--   A contact vector equals its global-frame coordinates times the global frame
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $x\in S$, and let $Z_1(x),Z_2(x)$ be Hryniewicz's global frame of $\xi$. Every $w\in\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$ is recovered from its global-frame coordinates: if $a+ib$ is the coordinate of $w$ (so $a=\omega_0(w,Z_2)$, $b=\omega_0(Z_1,w)$), then $w=a\,Z_1(x)+b\,Z_2(x)$.
--
--   This identifies $\xi_x$ with $\mathbb{C}$ through the global frame, so that statements about sections of $\xi$ can be read in coordinates.
--
--   **Formalization Note** The coordinate is `xiCoordC H x w` of `FiniteEnergyPlane_Winding`; the frame vectors are `HryniewiczCriterion.xiFrame1/2` of `H ∘ ofR4` at `toR4 x`, read back in `V 1` by `ofR4`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2 and Remark 2.13 (global frame of the contact structure)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- A vector `w ∈ ξ_x` (`x ∈ S`) is recovered from its coordinates in Hryniewicz's global
frame: `w = a Z₁ + b Z₂` with `a + i b = xiCoordC H x w`. -/
theorem eq_xiCoordC_smul_xiFrame (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {x w : V 1}
    (hx : H x = 1) (hw : IsInXi H x w) :
    w = (xiCoordC H x w).re • ofR4 (HryniewiczCriterion.xiFrame1 (fun z => H (ofR4 z)) (toR4 x)) +
      (xiCoordC H x w).im • ofR4 (HryniewiczCriterion.xiFrame2 (fun z => H (ofR4 z)) (toR4 x)) := by
  sorry

end FiniteEnergyPlane
