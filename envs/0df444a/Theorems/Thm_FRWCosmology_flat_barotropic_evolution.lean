-- Prove2me | Theorems.Thm_FRWCosmology_flat_barotropic_evolution
-- name    : FRWCosmology.flat_barotropic_evolution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:48:32.811726+00:00
-- url     : https://prove2.me/theorems/a4f003be-5ee1-4a8b-995b-1470a400fb81
-- title:
--   Evolution of a flat barotropic FRW universe: $a \propto (t-t_0)^{2/3(1+w)}$, $\rho \propto (t-t_0)^{-2}$
-- statement:
--   **Goal theorem of the mission.** Let a flat FRW universe ($K = 0$) with $G > 0$ carry a
--   barotropic fluid with linear equation of state $p = w\rho$, where $w \neq -1$, and assume
--   the energy density is positive throughout the domain $I$. Then there is a time $t_0$, not
--   belonging to $I$, such that for all $s, t \in I$
--
--   $$a(t) \;=\; a(s)\left(\frac{t-t_0}{s-t_0}\right)^{\frac{2}{3(1+w)}}, \qquad
--   \rho(t) \;=\; \rho(s)\left(\frac{s-t_0}{t-t_0}\right)^{2} .$$
--
--   These are eqs. (4.37) and (4.38) of the source: the scale factor follows a power law in the
--   time elapsed since the singularity at $t_0$, and the density falls off as the inverse square
--   of that time. Taking $w = 0$ gives the matter-dominated universe $a \propto t^{2/3}$ and
--   $w = 1/3$ the radiation-dominated universe $a \propto t^{1/2}$. The statement is phrased as
--   a ratio between two times of the domain, so that no normalization constant is fixed and the
--   base of the real power is always positive.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, p. 63, eqs. (4.37) and (4.38)

import Definitions.Def_FRWUniverse

namespace FRWCosmology

theorem flat_barotropic_evolution (U : FRWUniverse) (hG : 0 < U.G) (hK : U.K = 0) (w : ℝ)
    (hw : w ≠ -1) (heos : U.LinearEoS w) (hrho : ∀ t ∈ U.I, 0 < U.rho t) :
    ∃ t₀ : ℝ, (∀ t ∈ U.I, t ≠ t₀) ∧
      ∀ s ∈ U.I, ∀ t ∈ U.I,
        U.a t = U.a s * ((t - t₀) / (s - t₀)) ^ (2 / (3 * (1 + w))) ∧
        U.rho t = U.rho s * ((s - t₀) / (t - t₀)) ^ 2 := by sorry

end FRWCosmology
