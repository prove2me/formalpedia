-- Prove2me | Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_of_isFastPlane
-- name    : FiniteEnergyPlane.piDs_ne_zero_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T12:29:30.915514+00:00
-- url     : https://prove2.me/theorems/bcc4143e-0f27-45f9-8cc3-21e429bef169
-- title:
--   The ξ-part of the derivative of a fast plane vanishes nowhere
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. If $u$ is a fast finite-energy plane and $w=\mathrm{proj}\circ u$, then $\pi\,\partial_s w(z)\neq 0$ for every $z\in\mathbb{C}$, where $\pi$ is the projection onto $\xi$ along the Reeb field.
--
--   Role: this is the pointwise form of the condition $\mathrm{wind}_\pi(u)=0$ in the definition of a fast plane, and it is the input for the immersion and transversality properties of $w$.
--
--   **Formalization Note.** `piDs H u z` is $\pi\,\partial_s w(z)$ expressed in the global complex frame of $\xi$ (`xiCoordC`), as defined in `Definitions.Def_FiniteEnergyPlane_Winding`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), arXiv:0812.4076, Section 1 and Definition 2.14

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- On a fast finite-energy plane, the `ξ`-component `π ∂ₛw` of the derivative of
`w = proj ∘ u` vanishes nowhere. -/
theorem piDs_ne_zero_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hfast : IsFastPlane H J u) (z : ℂ) : piDs H u z ≠ 0 := by
  sorry

end FiniteEnergyPlane
