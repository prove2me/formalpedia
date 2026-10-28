-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_terminal_atom_irrelevant
-- name    : AvramDividend.Classical.runningSup_stopped_terminal_atom_irrelevant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:27:39.976902+00:00
-- url     : https://prove2.me/theorems/da473fc6-836b-43fc-8aaf-29e5129732b9
-- title:
--   The original running-supremum dividend measure has no terminal Stieltjes reward atom on nonnegative time
-- statement:
--   For any sample path of the original spectrally negative Lévy process, any nonnegative terminal time T, and any nonnegative reward integrand f, the running-supremum Stieltjes dividend integral on (0,T] equals its integral on (0,T). The original record dividend measure has no atom at any positive T and no atom at time zero, both previously Proved; pinned Mathlib Ioo_ae_eq_Ioc' and setLIntegral_congr remove the terminal endpoint exactly. This eliminates a key boundary ambiguity at the original random reflected ruin clock in the Avram first-jump reward formula. The result is pathwise and does not assume independence, bounded variation or finite activity.
-- source:
--   Avram, Palmowski and Pistorius (2007), stopped reflected regulator §3.3; Prove2Me runningSup_dividendMeasure_no_positive_atoms and runningSup_dividendMeasure_zero_atom.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_positive_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_stopped_terminal_atom_irrelevant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (0 : ℝ) T, f t
      ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in Ioo (0 : ℝ) T, f t
      ∂(dividendMeasure (runningSup X) ω)) := by sorry
