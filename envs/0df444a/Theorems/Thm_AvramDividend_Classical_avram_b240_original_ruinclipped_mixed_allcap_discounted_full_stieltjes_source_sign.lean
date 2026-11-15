-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
-- name    : AvramDividend.Classical.avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:17:17.785447+00:00
-- url     : https://prove2.me/theorems/fe0b56a6-3222-4c87-a14c-9d5f010c8f21
-- title:
--   Original mixed ruin-clipped all-cap discounted full-Stieltjes cash and physical source frozen-right-dividend signed nonpositivity
-- statement:
--   For original spectrally negative Lévy X, actual admissible D and any cap C including infinity, extend the original candidate w linearly above finite C and retain w when C is infinity. At every genuine pre-ruin interval (a,b], the full original discounted dividend Stieltjes cash plus the left-discounted difference of actual caplinear postpayment potential at the frozen Lévy source endpoint and the earlier dividend right limit is nonpositive. This handles full continuous and atomic payments within a physical cell, and preserves the real capped continuation and zero-time boundary. It forms the discounted Stieltjes correction needed to combine B238 physical source telescope and B239 signed HJB/right jump mesh for B236.
-- source:
--   Instantiate the Proved original allcap left-discounted full Stieltjes signed source theorem with V(z)=w(z) for C=top and the exact linear continuation above the original finite admissible cap otherwise; both required continuation equations follow by simplification. No post-ruin interval and no artificial replacement cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨
      (b : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
         V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by sorry
