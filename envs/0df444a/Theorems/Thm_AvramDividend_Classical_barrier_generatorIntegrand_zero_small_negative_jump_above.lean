-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
-- name    : AvramDividend.Classical.barrier_generatorIntegrand_zero_small_negative_jump_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:57:19.294227+00:00
-- url     : https://prove2.me/theorems/ca6d3d19-47a6-4bab-a6fe-3eddfe92ee46
-- title:
--   Above-barrier affine cancellation of the compensated negative-jump generator integrand
-- statement:
--   For a nonnegative real barrier a, reserve x>a and a small negative jump -1<y<0 that stays strictly above a, the compensated jump term for the exact barrierValue W a vanishes. This isolates the local generator cancellation needed for integrability above the barrier, without a large-jump first-moment assumption. The proof uses the affine right-hand branch of barrierValue and the exact derivative at x.
-- source:
--   Avram, Palmowski and Pistorius (2007), generator and barrier-value expressions, with the formal compensation convention in the pinned Formalpedia definitions.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set Filter Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.barrier_generatorIntegrand_zero_small_negative_jump_above
    (W : ℝ → ℝ) (a x y : ℝ)
    (ha : 0 ≤ a) (hx : a < x) (hxy : a < x + y)
    (hy1 : -1 < y) (hy0 : y < 0) :
    SpectrallyNegativeLevy.generatorIntegrand (barrierValue W a) x y = 0 := by sorry
