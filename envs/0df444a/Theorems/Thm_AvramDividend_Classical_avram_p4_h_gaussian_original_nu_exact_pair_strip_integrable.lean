-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_exact_pair_strip_integrable
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_nu_exact_pair_strip_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:49:44.4294+00:00
-- url     : https://prove2.me/theorems/50053141-7b20-459a-8b81-f9f607f85ab6
-- title:
--   Unconditional original Lévy quadratic integrability on the exact cutoff-pair small-jump band
-- statement:
--   For every pair of cutoffs n and m, the original source Lévy measure X.ν has finite real quadratic mark energy on the exact Ioc strip from the lower index minimum to upper index maximum. This is unconditional, includes the upper cutoff atom, and follows from the Proved genuine original quadratic tail integrability theorem by measurable set restriction. It discharges hSourceEnergy in the original intrinsic real L2 transfer.
-- source:
--   Original source X.ν quadratic real energy theorem 5dc7c9ac-0939-48ad-bb94-e7f676b51611, pinned Mathlib IntegrableOn.mono_set, elementary negative cutoff ordering.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_nu_exact_pair_strip_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / (((min n m : ℕ) : ℝ) + 1)))
           (-(1 / (((max n m : ℕ) : ℝ) + 1)))) X.ν := by sorry
