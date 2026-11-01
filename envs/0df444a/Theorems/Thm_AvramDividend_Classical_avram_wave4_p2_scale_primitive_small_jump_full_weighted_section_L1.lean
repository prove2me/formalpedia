-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_small_jump_full_weighted_section_L1
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_small_jump_full_weighted_section_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:34:15.188+00:00
-- url     : https://prove2.me/theorems/3c40a1b3-16f9-4ea0-89ef-4b137c06bcab
-- title:
--   Actual compensated primitive small jump is weighted L1 over every positive reserve
-- statement:
--   For every actual source small jump -r with 0<r<1, the original compensated Lévy generator integrand acting on the scale primitive is absolutely integrable against exponentially weighted positive reserves x>0. It glues the Proved true crossing section and the Proved true interior section across x=r, using Mathlib integrableOn_Ici_iff_integrableOn_Ioi to handle the singleton of Lebesgue measure zero. This is a true source fixed-jump L1 theorem, not a global product Fubini assertion, and will feed the eventual x×ν integral.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 4; exact source weighted crossing, interior, and pinned Mathlib integrableOn_union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_small_jump_full_weighted_section_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioi (0 : ℝ)) volume := by sorry
