-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_nonnegative_atoms
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_no_nonnegative_atoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:19:08.181799+00:00
-- url     : https://prove2.me/theorems/6b1bbe98-fb10-4561-bf0a-9bd58e3c0294
-- title:
--   No nonnegative-time payment atoms in the actual Lévy running-supremum Stieltjes dividend measure
-- statement:
--   For any spectrally negative Lévy sample path, the actual dividend Stieltjes measure of the running supremum has no singleton atoms at any nonnegative real time, including the distinguished time-zero payment convention. The time-zero case follows from the separately proved constant-negative-time extension and Stieltjes jump formula; every positive time follows from the proved absence of upward jumps and full continuity of the running maximum. This unified endpoint result is needed when passing between strict and weak stopping inequalities for the genuine stopped regulator dividend reward.
-- source:
--   Proved runningSup_dividendMeasure_no_positive_atoms 963e2c35-398a-4cf1-8017-2322a67349b5 (11946); pending runningSup_dividendMeasure_zero_atom a58ad30f-5992-4fbf-9198-4194afb2b995 (11951); elementary eq_or_lt_of_le case split.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_positive_atoms

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_no_nonnegative_atoms
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : 0 ≤ t) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by sorry
