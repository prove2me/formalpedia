-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_clm_boundedContinuous_rep
-- name    : FiniteEnergyPlane.exists_clm_boundedContinuous_rep
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T22:24:33.308718+00:00
-- url     : https://prove2.me/theorems/4fadead3-e138-453e-b849-8c6f0b61511e
-- title:
--   A continuous linear value map from the weighted unknowns to bounded continuous functions
-- statement:
--   There is a continuous linear map $U : W^{1,4} \times \mathbb{C} \times W^{1,4} \to C_b(\mathbb{R} \times \mathbb{R}, \mathbb{C}^3)$ (`QDom →L[ℝ] (ℝ × ℝ →ᵇ ℂ × ℂ × ℂ)`) such that for every $x = (\zeta_T, c, \zeta_N)$, $U(x) = (\zeta_T, \zeta_N, c)$ almost everywhere on the cylinder (first components of the $W^{1,4}$ triples, read in $\mathbb{C}$ via `vecToC`).
--
--   **Role.** The Sobolev embedding $W^{1,4} \hookrightarrow C_b$ on the cylinder, packaged as one bounded linear map on the unknowns, so that pointwise nonlinear expressions in the unknowns become superposition operators on $C_b$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

open MeasureTheory CauchyRiemannIndex
open scoped BoundedContinuousFunction

namespace FiniteEnergyPlane

/-- There is a continuous linear map `U` from `QDom = W^{1,4} × ℂ × W^{1,4}` to bounded continuous
functions on `ℝ × ℝ` with values in `ℂ × ℂ × ℂ` such that, for every `x = (ζT, c, ζN)`,
`U x = (ζT, ζN, c)` almost everywhere (first components of the `W^{1,4}` triples, read in `ℂ`). -/
theorem exists_clm_boundedContinuous_rep :
    ∃ U : QDom →L[ℝ] (ℝ × ℝ →ᵇ ℂ × ℂ × ℂ), ∀ x : QDom, ∀ᵐ q ∂cylMeasure,
      U x q = (vecToC ((x.1 : Triple 1 4).1 q), vecToC ((x.2.2 : Triple 1 4).1 q), x.2.1) := by
  sorry

end FiniteEnergyPlane
