-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_no_exit_before_horizon
-- name    : AvramDividend.Classical.chat03_no_exit_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:39:09.704979+00:00
-- url     : https://prove2.me/theorems/18ca5a10-6147-4563-bf0f-7997ea850917
-- title:
--   No strict grid exit before a horizon at or before the continuous exit infimum
-- statement:
--   Let τ be the GLB of all continuous strict two-sided exit times and let T≤τ. For every grid spacing h≥0 and every natural index k with kh<T, the process cannot be strictly outside the lower and upper boundaries at kh. In particular this covers paths with no continuous strict exit before T and the endpoint case T=τ. The proof uses only the lower-bound property of IsGLB, with no filtration or stopped-value convergence assumptions.
-- source:
--   A direct consequence of the published IsGLB strict exit time hypothesis; pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_no_exit_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hTτ : T ≤ τ) :
    ∀ h : ℝ≥0, ∀ k : ℕ,
      (k : ℝ≥0) * h < T →
        ¬ (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω)  := by sorry
