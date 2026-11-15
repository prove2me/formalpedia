-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
-- name    : AvramDividend.Classical.avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:57:50.632511+00:00
-- url     : https://prove2.me/theorems/def60518-0a6f-4add-a3fd-729fe4fb85f1
-- title:
--   Original pre-ruin signed Stieltjes dividend control at an arbitrary interior clipping cap
-- statement:
--   For an original spectrally negative Levy reserve with an admissible dividend strategy at cap C, the signed discounted Stieltjes dividend increment is nonpositive after applying a cap-linear test function V clipped at an arbitrary positive c. The admissible cap C is independent of the clipping cap c, so this covers the Gaussian finite-cap upper interior clipping b<C without silently assuming stronger admissibility.
-- source:
--   Specialisation of the Proved avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos: original admissibility IsAdmissibleLe X x C D supplies IsDividendStrategy and pre-ruin rightLimit D b <= x+X.X b independently of clipping c.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original Levy-source signed full-Stieltjes correction on each pre-ruin dividend interval. -/

theorem AvramDividend.Classical.avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by sorry
