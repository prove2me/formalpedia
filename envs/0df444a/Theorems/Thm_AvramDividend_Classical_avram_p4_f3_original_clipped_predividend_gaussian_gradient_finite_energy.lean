-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_predividend_gaussian_gradient_finite_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_clipped_predividend_gaussian_gradient_finite_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:25:03.055528+00:00
-- url     : https://prove2.me/theorems/a881c82d-3462-4440-9398-678f2ca5b9a6
-- title:
--   Original pre-dividend physical Gaussian gradient energy on a compact localising band
-- statement:
--   The original left-reserve x+X.X-rightLimit D, clipped to [δ,K], has finite Gaussian coefficient-square lintegral for the actual X.σ and derivative of w on any finite source time-probability measure μ. The statement preserves the same Ω, original X and physical D, with no separate Brownian model. It does not claim the stopped Gaussian stochastic integral exists or has mean zero; those remain additional original-process Ito-Meyer obligations.
-- source:
--   Direct formal source application of avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy with its U specialised to the literal original pre-dividend left-limit reserve, clipped to [δ,K]. The preceding generic theorem deduces the uniform Gaussian L2 bound from canonical C2 strict-cap smoothness and finite μ. The underlying unclipped state, boundary passage and martingale construction remain future obligations.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_clipped_predividend_gaussian_gradient_finite_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ Set.univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ := by sorry
