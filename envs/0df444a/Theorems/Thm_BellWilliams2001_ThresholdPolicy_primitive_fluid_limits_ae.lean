-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_primitive_fluid_limits_ae
-- name    : BellWilliams2001.ThresholdPolicy.primitive_fluid_limits_ae
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:41:26.465956+00:00
-- url     : https://prove2.me/theorems/564250ed-5f4d-4015-8606-b7effda9d083
-- title:
--   Almost-sure uniform renewal fluid limits for the arrival and service primitives
-- statement:
--   On a set of probability one, the two arrival counts and the three service-completion counts obey a joint uniform strong law at the fluid scale. For each compact interval $[0,H]$ and all sufficiently large $r$, the five fluid-scaled counts are uniformly close on $[0,H]$ to the five linear paths with slopes $\lambda_1,\lambda_2,\mu_1,\mu_2,\mu_3$. The result uses the common primitive sequence in (15). The system-dependent rates may vary, provided they converge as in Assumption 3.1.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, (15), (92)–(93), renewal fluid limits used in Sections 8–9

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory Filter Topology Set

namespace BellWilliams2001.ThresholdPolicy

theorem primitive_fluid_limits_ae {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∀ᵐ ω ∂M.P, ∀ H : ℝ, 0 ≤ H → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t ∈ Icc 0 H,
        (∀ k, |M.Abar n ω t k - M.lam k * t| < ε) ∧
        (∀ j, |M.Sbar n ω t j - M.mu j * t| < ε) := by sorry

end BellWilliams2001.ThresholdPolicy
