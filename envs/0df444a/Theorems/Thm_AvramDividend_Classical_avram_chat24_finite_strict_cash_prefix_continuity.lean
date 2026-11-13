-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_finite_strict_cash_prefix_continuity
-- name    : AvramDividend.Classical.avram_chat24_finite_strict_cash_prefix_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:49:12.763414+00:00
-- url     : https://prove2.me/theorems/088ef1db-eb6d-4350-aecb-a9a67900fb9d
-- title:
--   AvramDividend.Classical.avram_chat24_finite_strict_cash_prefix_continuity
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_finite_strict_cash_prefix_continuity from oversized parent candidate 21c373232a39d2b64e926d1157847e109e232fdf8ef687b7a8d732984cf5180b.
-- source:
--   candidate-decomposition:fcea3ff9-d1d8-4e51-a67b-ca75c8c222e9:21c373232a39d2b64e926d1157847e109e232fdf8ef687b7a8d732984cf5180b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem AvramDividend.Classical.avram_chat24_finite_strict_cash_prefix_continuity
    (m : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : AEMeasurable f m)
    (u : ℕ → ℝ) (t : ℝ) (hm : Monotone u)
    (hu : ∀ n, u n < t) (hl : Tendsto u atTop (nhds t))
    (hfinite : (∫⁻ y in Ico 0 t, f y ∂m) ≠ ⊤) :
    Tendsto (fun n => (∫⁻ y in Ico 0 (u n), f y ∂m).toReal) atTop
      (nhds (∫⁻ y in Ico 0 t, f y ∂m).toReal) := by sorry
end
