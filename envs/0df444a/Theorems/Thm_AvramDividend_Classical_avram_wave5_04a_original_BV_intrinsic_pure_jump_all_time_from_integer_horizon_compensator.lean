-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_BV_intrinsic_pure_jump_all_time_from_integer_horizon_compensator
-- name    : AvramDividend.Classical.avram_wave5_04a_original_BV_intrinsic_pure_jump_all_time_from_integer_horizon_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:14:15.763506+00:00
-- url     : https://prove2.me/theorems/d4b663c9-fc3a-4864-80c5-92b53f320873
-- title:
--   Actual BV Lévy pure-jump equality for all times reduced to integer-horizon intrinsic compensator identities
-- statement:
--   For the actual original Standing bounded-variation spectrally negative Levy process, if at each natural-number horizon the physical source equals drift times time minus its exact original intrinsic negative-jump integral almost surely, then a single probability-one event has this equality at every nonnegative real time. The pre-existing zero-anchored residual R is nonnegative, nondecreasing and zero at zero; integer-horizon identities force R(n)=0, and every real time is below some integer. The new theorem is a conditional reduction: it exposes the exact same-process integer-horizon compensator identity still missing, without assuming the desired equality at all times or constructing any replacement Poisson process.
-- source:
--   Chat04-A source-only conditional normalisation bridge. Reuses canonical Proved zero-anchored original BV source residual 93ee4a8c-bc51-4b92-ad77-e9fcff70bbd6, plus pinned Mathlib countable almost-everywhere intersection MeasureTheory.ae_all_iff. The remaining input is the genuine original intrinsic Lévy jump-magnitude first moment/compensator at each integer, not a copied process or a presumed all-time equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Same-original-source reduction of all-time pure-jump equality to countably many integer-horizon intrinsic compensator identities. -/

theorem AvramDividend.Classical.avram_wave5_04a_original_BV_intrinsic_pure_jump_all_time_from_integer_horizon_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hIntegers : ∀ n : ℕ, ∀ᵐ ω ∂P,
      X.X (n : ℝ≥0) ω =
        ((n : ℝ≥0) : ℝ) * X.drift -
          (∫⁻ p,
            (if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) then
              ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∫⁻ p,
          (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
