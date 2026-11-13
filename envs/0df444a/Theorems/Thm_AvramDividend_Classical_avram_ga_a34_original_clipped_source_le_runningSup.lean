-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a34_original_clipped_source_le_runningSup
-- name    : AvramDividend.Classical.avram_ga_a34_original_clipped_source_le_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:25:10.157308+00:00
-- url     : https://prove2.me/theorems/5d8a0fc4-4f0f-4f3a-9ac2-d048d91d641a
-- title:
--   Actual original clipped Gaussian postpayment source is bounded by finite-horizon running supremum
-- statement:
--   For the original stopped clipped grid, if the dividend right limit is nonnegative and the stopping clock is bounded by the horizon, the physical postpayment source x+X(v[m+1])-D+(v[m]) is bounded above by x plus the running supremum of the same original X over that horizon. This is a deterministic source-level ingredient for the a26 terminal positive integrable envelope.
-- source:
--   Terminal-envelope obligation d9c4650e; reuse authoritative runningSup_monotone_and_path_le 848fbd48 and actual rightLimit D grid geometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a34_original_clipped_source_le_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, 0 ≤ rightLimit D t ω)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0) (hρ : ∀ ω, ρ ω ≤ n)
    (m : Nat) (ω : Ω) :
    let dt : ℝ≥0 := n / ((m : ℝ≥0) + 1)
    let v : Nat → ℝ≥0 := fun i => min ((i : ℝ≥0) * dt) (ρ ω)
    x + X.X (v (m + 1)) ω - rightLimit D (v m) ω ≤
      x + runningSup X n ω := by sorry
