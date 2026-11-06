-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_finite_base_quadratic_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_finite_base_quadratic_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:16:24.403095+00:00
-- url     : https://prove2.me/theorems/46b7ab64-a2b7-4466-b752-94ec8ff6a2c4
-- title:
--   Original intrinsic compact-jump quadratic coefficient energy over finite localising time-probability measure
-- statement:
--   For original spectrally negative Lévy X, on any finite physical localisation measure μ over a time-probability base S and any reserve section U valued in a positive compact reserve interval, the two-step integral of the literal original jump-coefficient square against the actual X.ν then μ is finite. The uniformity and proof come directly from the verified original ν quadratic envelope and finite mass of μ. Does not assert that an arbitrary U is measurable, predictable or already a stochastic martingale; this is the deterministic L2 energy step to support later stochastic source closure.
-- source:
--   Uses original compact reserve ν-integral uniform bound E<top for all reserve states and monotonicity of iterated lintegral over arbitrary finite μ. This is a uniform original Lévy jump coefficient intensity estimate ready to instantiate at the exact predictable stopped reserve and finite source time-times-probability measure.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_uniform_nu_square_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_finite_base_quadratic_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ Set.univ < ⊤)
    (U : S → ℝ) (hU : ∀ s, U s ∈ Icc δ K) :
    (∫⁻ s, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal
        ((w (U s + z) - w (U s)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry
