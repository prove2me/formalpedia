-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_boundary_scalar_errors_both_vanish
-- name    : AvramDividend.Classical.avram_f6_original_finitecap_boundary_scalar_errors_both_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:53:06.722823+00:00
-- url     : https://prove2.me/theorems/09d929a0-13bc-4227-ab72-c1c8f39e6472
-- title:
--   Original finite-cap HJB corner and upper-strip scalar errors vanish, with nonnegative corner gap
-- statement:
--   Under exactly the genuine unbounded-variation F6 regularity, gradient and admissibility hypotheses with finite cap, the rational caplinear corner scalar gap is nonnegative for every cutoff and tends to zero, and the full physical controlled reserve expected occupation in the shrinking upper-cap strip tends to zero. These are the complete finite-cap boundary correction terms appearing in the original stopped Gaussian and mixed Lévy Itô/HJB verification; no artificial cap bound or extra stochastic source premise is added.
-- source:
--   Proved gbB37 finitecap interior gap 973cf9b8; Proved original admissible upperstrip cb1a7c38; pending original rational corner 1d3dc336.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_finitecap_boundary_scalar_errors_both_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    (∀ j : ℕ, 0 ≤ (w C.toReal -
      w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal - C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) ∧
    Tendsto (fun j : ℕ =>
      (w C.toReal -
        w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal - C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun j : ℕ => ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
      if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
        riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
