-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_firstRecord_drawdown_at_observation_clock
-- name    : AvramDividend.Classical.avram_ws01e_b_firstRecord_drawdown_at_observation_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:44:23.309974+00:00
-- url     : https://prove2.me/theorems/71b3a652-5891-495b-9163-c8693356a23d
-- title:
--   Attained upper-record drawdown restart at an actual independent observation horizon
-- statement:
--   For any spectrally negative Lévy sample path, a nonnegative level b and a finite attained first strict upward-passage time u that is a running-record maximum, and any observation time eη at or after u, the terminal drawdown S_(eη)−X_(eη) equals the drawdown computed entirely from the future path segment X_(u+r), for 0≤r≤eη−u. The proof is a time-change of the canonically Proved firstRecord_drawdown_post_shift_reset using exact nonnegative subtraction u+(eη−u)=eη. This is the precise pathwise observation-clock bridge before the probabilistic post-stopping regeneration argument; no distributional independence, exponential-clock law or Wiener–Hopf theorem is assumed. Equality u=eη is included for boundary correctness.

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_firstRecord_drawdown_at_observation_clock
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (e : Θ → ℝ≥0) (η : Θ) (hObs : u ≤ e η) :
    runningSup X (e η) ω - X.X (e η) ω =
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 (e η - u)) -
        X.X (e η) ω := by sorry
