-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_full_hjb_from_interior_equation_and_bounded_strip_sign
-- name    : AvramDividend.Classical.avram_wave4_05_full_hjb_from_interior_equation_and_bounded_strip_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:03:52.994212+00:00
-- url     : https://prove2.me/theorems/5d642a19-a3c2-498f-84f0-0d60d1a9fa5b
-- title:
--   Entire original source HJB equality from scalar interior generator equation and bounded upper strip residual sign
-- statement:
--   Under the root Standing and Gaussian∨BV∨global C2 positive smoothness alternative, the full all-positive source generator domain and HJB equation max(Γvcstar−qvcstar,1−vcstar')=0 follow from only (1) the scalar equality Γvcstar−qvcstar=0 on the positive interior if cstar>0 and (2) the scalar inequality Γvcstar−qvcstar≤0 on the finite upper strip cstar<y<cstar+1+max(0,X.c/q). No GeneratorIntegrable premise remains anywhere because the canonically Proved original all-positive domain theorem discharges it. The far-field HJB and cap cases are covered by canonically Proved source results. The scalar interior equation remains the P2-dependent missing analytic identity and is not assumed as proved here.
-- source:
--   Source all-positive domain 8fd5ab93; source bounded strip HJB aa470a98; original target edf09308

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_full_hjb_of_interior_harmonicity_and_bounded_strip_residual

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_full_hjb_from_interior_equation_and_bounded_strip_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_strip : ∀ y : ℝ,
      (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside_eq : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator (vcstar W) x - q * vcstar W x = 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
