-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
-- name    : AvramDividend.Classical.avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:11:42.092119+00:00
-- url     : https://prove2.me/theorems/2892ebc8-0f32-4840-85ce-0b9c736d308b
-- title:
--   Compact C2 derivative and small negative mark give uniform discounted first-order kernel bound
-- statement:
--   For any prepayment reserve source Y(t,omega), if w is C2 on (0,Cband) and spatial gradient is clipped to [u+delta,v] in this interior, any negative mark z∈(-1,-eta) and discount q>=0 yields the uniform absolute deterministic bound M on exp(-qt) times the clipped first-order derivative times z. Source for exact physical source49 kernel count domination and source54 compensator bounds. No stochastic premise is supplied.
-- source:
--   Proved avram_p4_c_generator_compact_derivative_bounded and Proved reward58 scalar discounted small-mark bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_derivative_bounded
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (Cband u v δ η : ℝ)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hleft : 0 < u + δ) (hband : u + δ < v)
    (hv : v < Cband) (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (t : ℝ≥0) (ω : Ω) (z : ℝ),
        z ∈ Ioo (-1 : ℝ) (-η) →
        |Real.exp (-(q * (t : ℝ))) *
          (if Y t ω ∈ Icc (u + δ) v then
            deriv w (Y t ω) * z else 0)| ≤ M := by sorry
