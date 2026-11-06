-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
-- name    : AvramDividend.Classical.avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:53:51.714618+00:00
-- url     : https://prove2.me/theorems/b065494f-500f-4b86-a416-cac58c968903
-- title:
--   Original Lévy source martingale physical-grid increment conditional mean zero
-- statement:
--   A genuine original-process martingale indexed by nonnegative real times and adapted to the original right-continuous Lévy filtration has zero conditional mean on every chronological physical-grid increment Y(u_{i+1})-Y(u_i), provided u is monotone. This supplies the missing source conditional centering assumption in original predictable stopped-grid signed budgets when Y is an established martingale.
-- source:
--   Pinned Mathlib Martingale.condExp_ae_eq, condExp_sub and original SpectrallyNegativeLevy.isProbability; no equality-in-law substitution. The martingale property itself remains a genuine original-source hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (i : ℕ) :
    P[(fun ω => Y (u (i + 1)) ω - Y (u i) ω) | 𝓕.rightCont (u i)]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
