-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_upper_by_interior_cap
-- name    : AvramDividend.Classical.avram_mix_fin26_original_reward_upper_by_interior_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:59:31.380416+00:00
-- url     : https://prove2.me/theorems/395ef91e-100b-4b44-9501-fd57a271403e
-- title:
--   Original mixed finite-cap gradient yields reward bound on every compact interior interval
-- statement:
--   From source-exact C2 smoothness, continuity on nonnegative reserve and gradient >=1 before the cap, any real 0<u<v with ofReal(v)<cap satisfies w(y)<=w(v) for all y in [u,v). Restrict the C2 domain to the open interior (u,v), derive the full derivative, then apply the already-Proved Gaussian closed-cap gradient growth lemma, which yields v-y<=w(v)-w(y). This supplies the missing upper-reward premise of the mixed HJB derivative estimate with W=w(v), without assuming differentiability at the cap.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_gradient_growth_to_cap
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_original_reward_upper_by_interior_cap
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v : ℝ) (hu : 0 < u) (huv : u < v)
    (hvC : ENNReal.ofReal v < C) :
    ∀ y ∈ Ico u v, w y ≤ w v := by sorry
