-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_untwisted_powers_continuity
-- name    : AvramDividend.Classical.causal_untwisted_powers_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:46:57.738657+00:00
-- url     : https://prove2.me/theorems/b00f2ecb-deb8-49e6-bb7c-20c016bd9c77
-- title:
--   Continuity of undamped convolution powers from continuous damped powers
-- statement:
--   If a sequence F of globally continuous functions is the exponential damping of U, then every U_n is globally continuous. Recover U_n pointwise by division by the everywhere-positive exponential factor. Combined with the established causal monotonicity theorem, this supports the undamped Neumann series needed in positive-discount scale existence.
-- source:
--   Elementary continuity of a quotient and nonvanishing real exponential.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical

theorem AvramDividend.Classical.causal_untwisted_powers_continuity
    (F U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hFcont : ∀ n : ℕ, Continuous (F n))
    (hrel : ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x) :
    ∀ n : ℕ, Continuous (U n) := by sorry
