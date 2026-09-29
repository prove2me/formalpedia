-- Prove2me | Theorems.Thm_FRWCosmology_hubble_power_law
-- name    : FRWCosmology.hubble_power_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:47:42.865603+00:00
-- url     : https://prove2.me/theorems/7a220520-c80c-4cf4-8f51-547a48ebf1aa
-- title:
--   Hubble parameter $H = \frac{2}{3(1+w)(t-t_0)}$ of a flat barotropic universe
-- statement:
--   Let a flat FRW universe ($K = 0$) with $G > 0$ carry a barotropic fluid with linear equation
--   of state $p = w\rho$, where $w \neq -1$, and assume the energy density is positive
--   throughout the domain. Then there is a constant $t_0$ such that for every time $t$ of the
--   domain
--
--   $$H(t) \;=\; \frac{2}{3(1+w)\,(t-t_0)} .$$
--
--   Combining the Friedmann equations gives $\dot H = -\tfrac32(1+w)H^2$ with $H^2 > 0$, so
--   $1/H$ has constant derivative $\tfrac32(1+w)$; integrating produces the constant $t_0$, the
--   time of the Big-Bang singularity, which necessarily lies outside the domain.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, p. 62, eq. (4.36)

import Definitions.Def_FRWUniverse

namespace FRWCosmology

theorem hubble_power_law (U : FRWUniverse) (hG : 0 < U.G) (hK : U.K = 0) (w : ℝ) (hw : w ≠ -1)
    (heos : U.LinearEoS w) (hrho : ∀ t ∈ U.I, 0 < U.rho t) :
    ∃ t₀ : ℝ, ∀ t ∈ U.I, U.H t = 2 / (3 * (1 + w) * (t - t₀)) := by sorry

end FRWCosmology
