-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_mapped_positive_clock_integral_zero
-- name    : AvramDividend.Classical.avram_chat24_mapped_positive_clock_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:14:01.734699+00:00
-- url     : https://prove2.me/theorems/64c355a6-aa53-465f-9bf0-a25162cf26ce
-- title:
--   AvramDividend.Classical.avram_chat24_mapped_positive_clock_integral_zero
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_mapped_positive_clock_integral_zero from oversized parent candidate d6cf3531c246d9a1a82e3e4eb6811415688d59ae1624a9e146f0c763af9a2f12.
-- source:
--   candidate-decomposition:235cf812-5f12-4e32-b966-4b84acac62f3:d6cf3531c246d9a1a82e3e4eb6811415688d59ae1624a9e146f0c763af9a2f12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem AvramDividend.Classical.avram_chat24_mapped_positive_clock_integral_zero
    (m : Measure ℝ≥0) (s : Set ℝ≥0) (j : ℝ≥0 → ℝ) (F : ℝ≥0 × ℝ → ℝ)
    (hs : s ⊆ Ioi 0) (hF : ∀ p, p.1 ≠ 0 → F p = 0) :
    (∫ p, F p ∂((m.restrict s).map (fun u => (u, j u)))) = 0 := by sorry
end
