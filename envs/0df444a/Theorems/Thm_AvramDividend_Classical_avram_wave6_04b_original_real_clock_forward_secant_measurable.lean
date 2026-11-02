-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_original_real_clock_forward_secant_measurable
-- name    : AvramDividend.Classical.avram_wave6_04b_original_real_clock_forward_secant_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:52:07.570689+00:00
-- url     : https://prove2.me/theorems/9d85d0f2-dcd2-486b-bbb2-8d286873e4ce
-- title:
--   Actual original real-clock Stieltjes forward-secant correction is measurable
-- statement:
--   For a genuine original Lévy process and dividend strategy, the discounted forward-secant correction against the exact right-limit post-payment reserve is Borel measurable in real Stieltjes time whenever its potential extension V is Borel measurable. It uses the source-specific càdlàg/adapted real-clock reserve lemma, and requires no dividend rate, strict-interior occupation, or derivative at zero or cap. This is the measurability bridge for finite-horizon actual signed Stieltjes integrability.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- The genuine original-source post-payment real-clock forward
--   secant integrand is Borel measurable whenever the extension V is Borel. -/
--   theorem AvramDividend.Classical.avram_wave6_04b_original_real_clock_forward_secant_measurable
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
--       (hD : IsDividendStrategy 𝓕 D)
--       (ω : Ω) (q δ : ℝ) (V : ℝ → ℝ)
--       (hVmeas : Measurable V) :
--       Measurable (fun s : ℝ =>
--         Real.exp (-(q * s)) *
--           (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
--             V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))) := by
--     let F : ℝ → ℝ := fun s =>
--       x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω
--     have hF : Measurable F :=
--       avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
--         X x D hD ω
--     have hExp : Measurable (fun s : ℝ => Real.exp (-(q * s))) :=
--       Real.continuous_exp.measurable.comp
--         ((measurable_const.mul measurable_id).neg)
--     have hVf : Measurable (fun s : ℝ => V (F s)) :=
--       hVmeas.comp hF
--     have hVfd : Measurable (fun s : ℝ => V (F s + δ)) :=
--       hVmeas.comp (hF.add measurable_const)
--     change Measurable (fun s : ℝ =>
--       Real.exp (-(q * s)) * (δ + V (F s) - V (F s + δ)))
--     exact hExp.mul ((measurable_const.add hVf).sub hVfd)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_original_real_clock_postpayment_reserve_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_04b_original_real_clock_forward_secant_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q δ : ℝ) (V : ℝ → ℝ)
    (hVmeas : Measurable V) :
    Measurable (fun s : ℝ =>
      Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
          V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))) := by sorry
