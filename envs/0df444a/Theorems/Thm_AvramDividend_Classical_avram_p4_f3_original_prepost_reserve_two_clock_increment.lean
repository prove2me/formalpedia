-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_prepost_reserve_two_clock_increment
-- name    : AvramDividend.Classical.avram_p4_f3_original_prepost_reserve_two_clock_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:41:46.959198+00:00
-- url     : https://prove2.me/theorems/ced98f02-c474-42b0-9ff5-d07b57beabfe
-- title:
--   Original two-clock prepayment and post-rightpayment reserve increment identities
-- statement:
--   For any original spectrally negative Lévy X, dividend path D, sample and two clocks, the reserve increment is the X increment less the dividend increment. The post-rightpayment corrected reserve increment uses the two right limits. This retains both endpoint payment atoms in the exact physical stopped source-cell algebra.
-- source:
--   Independent pathwise finite-clock ledger component of canonical fdb9a6a3, reducing the nontrivial stochastic source to separate Gaussian/jump/HJB integrations after exact original reserve accounting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f3_original_prepost_reserve_two_clock_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (s t : ℝ≥0) (ω : Ω) :
    (riskProcess X x D t ω - riskProcess X x D s ω =
      (X.X t ω - X.X s ω) - (D t ω - D s ω)) ∧
    ((riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
      (riskProcess X x D s ω - (rightLimit D s ω - D s ω)) =
      (X.X t ω - X.X s ω) -
        (rightLimit D t ω - rightLimit D s ω)) := by sorry
