-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger169_discount_exponential_Euler_quadratic_cell_all_scales
-- name    : AvramDividend.Classical.avram_gledger169_discount_exponential_Euler_quadratic_cell_all_scales
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:13:29.352488+00:00
-- url     : https://prove2.me/theorems/9fb30be1-273e-49eb-b9f9-fe8b5f1ed422
-- title:
--   Uniform exponential Euler quadratic cell error at every nonnegative mesh scale
-- statement:
--   Extends the already Proved small-cell exponential bound gledger145 to every nonnegative discount and mesh width, including coarse initial meshes. The exponential tangent inequality gives a nonnegative Taylor residual, bounded by the step itself for large steps, and the square dominates the step when the step is at least one. Needed to close the deterministic gledger164 finite-clipped discount rate through the already Proved finite aggregation lemma gledger149.
-- source:
--   Proved gledger145 on q delta <= 1, Mathlib exponential convexity/tangent inequality on q delta >= 1, source exact for physical uniform-grid steps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Real AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gledger169_discount_exponential_Euler_quadratic_cell_all_scales
    (q t δ : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    |Real.exp (-(q * (t + δ))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))| ≤ (q * δ) ^ 2 := by sorry
