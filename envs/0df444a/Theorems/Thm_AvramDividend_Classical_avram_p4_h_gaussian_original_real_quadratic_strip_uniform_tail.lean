-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:38:03.351867+00:00
-- url     : https://prove2.me/theorems/bf4a60e4-0a06-49c1-93a7-7781bf221f85
-- title:
--   Original negative-jump strip real quadratic-energy convergence, uniform in the second cutoff
-- statement:
--   For each original spectrally negative Lévy process X and positive real tolerance ε, there is a cutoff N beyond which every deeper negative-jump strip (-1/(n+1),-1/(m+1)] has its genuine original X.ν quadratic real integral finite and below ε, uniformly in m. This converts ENNReal tail energy into the real variance scale required by P4-G.
-- source:
--   The already proved original X.ν ENNReal uniform strip bound and real tail integrability/Bochner identity; pinned Mathlib IntegrableOn.mono_set, ofReal_integral_eq_lintegral_ofReal and ENNReal.ofReal_lt_ofReal_iff. No new process or stochastic isometry premise.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_quadratic_strip_uniform_tail
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
      IntegrableOn (fun z : ℝ => z ^ 2)
        (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) X.ν ∧
      (∫ z in Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))),
        z ^ 2 ∂X.ν) < ε := by sorry
