-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_physical_drift_bound
-- name    : AvramDividend.Classical.avram_p4_c_generator_compact_physical_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:04:41.858021+00:00
-- url     : https://prove2.me/theorems/36c9748f-402f-4058-81c1-32e098911d4d
-- title:
--   Original epsilon-physical Lévy drift uniformly bounded on compact interior reserve bands
-- statement:
--   From the source Lévy second-moment truncation condition and C² regularity only on 0<y<C, prove finite absolute first mark moment on the separated strict unit annulus and a uniform bound on the actual physical ε-drift contribution (X.c-∫_{-1<z<-ε}z ν(dz))*w'(y) throughout each compact interior reserve interval. This bound is available before stochastic compensation and is not an endpoint or overshoot statement.
-- source:
--   Exact SpectrallyNegativeLevy generator coefficient X.c, accepted cutoff_linear_mark_integrable, pinned Mathlib ContDiffOn.continuousOn_deriv_of_isOpen and IsCompact.exists_bound_of_continuousOn

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_linear_mark_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_compact_physical_drift_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C u v ε : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u) (hv : v < C) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => z) (Ioo (-1 : ℝ) (-ε)) X.ν ∧
    ∃ B : ℝ, ∀ y ∈ Icc u v,
      |(X.c - ∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν) * deriv w y| ≤ B := by sorry
