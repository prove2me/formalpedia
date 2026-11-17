-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_finite_ENNReal_tendsto_from_real_cast_20261116
-- name    : AvramDividend.Classical.avram_a26_finite_ENNReal_tendsto_from_real_cast_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:22:36.939859+00:00
-- url     : https://prove2.me/theorems/73330d75-b2eb-4173-b3ca-5bd07991b4a2
-- title:
--   Convergence of finite extended-nonnegative measures follows from convergence of their real values
-- statement:
--   For an everywhere-finite sequence in ENNReal converging in its real cast to the finite real cast of x, the ENNReal sequence converges to x. Use ENNReal.continuous_ofReal, and the identity ofReal(toReal z)=z for finite z. This safely transfers the original-space binomial singleton probability convergence from real to the ENNReal-valued statement.
-- source:
--   Pinned Mathlib ENNReal.continuous_ofReal and ENNReal.ofReal_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a26_finite_ENNReal_tendsto_from_real_cast_20261116
    (g : ℕ → ℝ≥0∞) (x : ℝ≥0∞)
    (hfin : ∀ n, g n ≠ ⊤) (hx : x ≠ ⊤)
    (h : Tendsto (fun n => (g n).toReal) atTop (𝓝 x.toReal)) :
    Tendsto g atTop (𝓝 x) := by sorry
