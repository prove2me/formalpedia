-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar
-- name    : AvramDividend.Classical.vcstar_monotone_of_finite_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:11:27.954276+00:00
-- url     : https://prove2.me/theorems/8a1169cb-22fd-4b52-b4b8-fdf06c536132
-- title:
--   Finite optimal barrier implies globally monotone dividend candidate
-- statement:
--   If cstar W is finite under the standing Lévy hypotheses, then the candidate value vcstar W is nondecreasing on the whole real line. The zero-barrier and positive-real-barrier cases have separately verified monotonicity proofs. Every finite nonzero extended-nonnegative barrier has a strictly positive real value, so those cases exhaust finite cstar and yield a global negative-jump comparison premise without further case splits.
-- source:
--   Proved vcstar_monotone_of_positive_real_cstar (d9b236d2-77d2-4838-b312-ed0e035175dd), newly submitted vcstar_monotone_of_zero_cstar (5e725b3c-cd63-447c-985c-593544993902), and pinned Mathlib ENNReal.toReal_pos.

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_monotone_of_finite_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤) :
    Monotone (vcstar W) := by sorry
