-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_zero_cstar
-- name    : AvramDividend.Classical.vcstar_monotone_of_zero_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:03:35.45198+00:00
-- url     : https://prove2.me/theorems/5e725b3c-cd63-447c-985c-593544993902
-- title:
--   Zero-barrier candidate value is monotone on the whole real line
-- statement:
--   The genuine optimal barrier value candidate is globally nondecreasing whenever the optimal barrier is zero and W is a standing q-scale function. On negative capital the candidate is zero; on nonnegative capital it is capital plus the nonnegative value at the boundary. Comparing all cross-zero and same-side pairs establishes global monotonicity and supplies the missing negative-jump comparison premise for far-field HJB verification.
-- source:
--   Canonically Proved barrierValue_zero_affine_nonnegative (f9262914-ea46-4333-87e2-0cd1ac57a1bc) and barrierValue_nonnegative_for_nonnegative_capital (861b7656-5bc3-4d92-81da-da184060de56).

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_monotone_of_zero_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0) :
    Monotone (vcstar W) := by sorry
