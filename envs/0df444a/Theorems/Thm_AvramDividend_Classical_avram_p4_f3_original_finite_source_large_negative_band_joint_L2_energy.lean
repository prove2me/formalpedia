-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_finite_source_large_negative_band_joint_L2_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_finite_source_large_negative_band_joint_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:17:58.807197+00:00
-- url     : https://prove2.me/theorems/b32fbc0c-c40c-451d-8e82-b4a41aa1e3fa
-- title:
--   Original large-negative Lévy source jump coefficient has finite joint quadratic energy on every finite physical time-sample measure
-- statement:
--   For the actual original Levy measure X.nu, finite physical time-sample source measure, and any original controlled reserve coefficient U bounded above by a finite cap, the full large-negative jump coefficient w(U+z)-w(U) is square-integrable jointly in source time and marks over every band separated from zero. The source coefficient may depend on both original time and sample and requires no independent-process law substitution.
-- source:
--   The accepted original uniform w-value squared kernel envelope c3b03f14 applies at each physical reserve U(p), and the original separated negative Borel Levy rate 86086cb2 is finite. Integrating the uniform bound over any finite source measure proves actual joint large-band quadratic energy for the missing Ml martingale. The source-declaration placeholder is intentionally separate from the sorry-free checked solution file.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_finite_source_large_negative_band_joint_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-ε))
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤)
    (U : ℝ≥0 × Ω → ℝ) (hU : ∀ p, U p ≤ K) :
    (∫⁻ p, (∫⁻ z in B,
      ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
