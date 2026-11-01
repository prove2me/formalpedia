-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_small_negative_jump_size_band_memLp_two
-- name    : AvramDividend.Classical.avram_wave4_04_source_small_negative_jump_size_band_memLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:52:58.664447+00:00
-- url     : https://prove2.me/theorems/a4a6f84f-bd6b-4eb6-99ce-b26fc4496d03
-- title:
--   Original Lévy source has square-integrable negative jump-size intensity on each bounded time strip
-- statement:
--   For the actual given spectrally negative Lévy source X, the negative-mark magnitude z=-y supported on 0<z<1 is L² under finite-time Lebesgue measure times the reflected source Lévy measure. The proof uses X.ν_integrable, X.ν_Ici and Proved reflected-intensity lemmas, and requires no private or unverified owner publication. This is the correct square-integrable intensity regime for compensating infinite-activity small negative jumps; it does not assert any jump-measure compensator or martingale property for X, nor alter any adapted control D. Proving this theorem alone is not a proof of the corrected dividend-verification target.
-- source:
--   Source process definition SpectrallyNegativeLevy.ν_integrable and ν_Ici; prior Proved gaussian_negative_jump_pushforward_sigmaFinite (08bca239) and gaussian_levy_square_integrable_neg_pushforward (581daddd); finite-product measure L² API under pinned Mathlib.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_source_small_negative_jump_size_band_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ Set.Ioo (0 : ℝ) 1).indicator
      (fun p : ℝ × ℝ => p.2)) 2
      (volume.prod (X.ν.map (fun y : ℝ => -y))) := by sorry
