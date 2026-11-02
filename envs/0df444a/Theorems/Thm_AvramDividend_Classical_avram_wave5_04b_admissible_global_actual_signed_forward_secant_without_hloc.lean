-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_admissible_global_actual_signed_forward_secant_without_hloc
-- name    : AvramDividend.Classical.avram_wave5_04b_admissible_global_actual_signed_forward_secant_without_hloc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:20:57.298382+00:00
-- url     : https://prove2.me/theorems/3b5c8e38-7927-474c-a960-0f39a1664b8f
-- title:
--   Original admissible capped dividend actual signed Stieltjes forward secant without hloc
-- statement:
--   For every original IsAdmissibleLe capped strategy, zero or strict pre-ruin closed horizon, positive finite/infinite cap and integrable derivative-free finite-difference control term, the signed actual dividendMeasure integral is nonpositive without any supplementary hSolvent, strict interior hloc, derivative at zero/cap, or atom-only assumption. Genuine postpayment solvency is derived from admissibility using the separately Proved closed-horizon solvency lemma. This is a regularised control sign input, not the stochastic Ito-Meyer identity.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- For genuinely admissible original source-X dividends, the actual real
--   Stieltjes signed forward-secant correction is nonpositive on the full closed
--   horizon, including boundary contacts and singular-continuous variation. -/
--   theorem solution
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
--       (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_smooth : ContDiffOn ℝ 1 w
--         {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
--       (hw_grad : ∀ z : ℝ, 0 < z →
--         ENNReal.ofReal z < C → 1 ≤ deriv w z)
--       (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
--       (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
--         V z = if z ≤ C.toReal then w z
--           else w C.toReal + (z - C.toReal))
--       (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
--       (ω : Ω) (T : ℝ≥0)
--       (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω)
--       (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
--           (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
--         (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
--       (∫ s in Icc (0 : ℝ) (T : ℝ),
--         Real.exp (-(q * s)) *
--           (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by
--     have hSolvent := avram_wave5_04b_closed_preruin_actual_postpayment_solvency
--       X x C D hD ω T hPre
--     exact avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos
--       X x C hC q δ hδ w V hw_cont hw_smooth hw_grad hVtop hVfinite
--       D ω T hSolvent hIntegrable

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_admissible_global_actual_signed_forward_secant_without_hloc

    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω)
    (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
    (∫ s in Icc (0 : ℝ) (T : ℝ),
      Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by sorry
