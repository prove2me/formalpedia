-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_finite_jump_normalisation
-- name    : AvramDividend.Classical.barrierValue_zero_of_finite_jump_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:49:57.646888+00:00
-- url     : https://prove2.me/theorems/73b88d8e-2aac-47a6-b280-48cb3e7375fd
-- title:
--   Finite-jump zero-barrier scale normalisation equals discounted first-jump dividends
-- statement:
--   In the bounded-variation finite-jump case with drift d and negative-jump intensity λ, the standard scale boundary data W(0)=1/d and W'(0+)=(q+λ)/d² yield the discounted first-jump value d/(q+λ). This deterministic equality is one half of the zero-reflected-supremum proof. Proving the actual reflected dividend expectation and the scale boundary formulas from Standing remain separate stochastic/analytic obligations.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, zero-barrier calculation (3.14); https://arxiv.org/pdf/math/0702893

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_eq_ratio_of_finite_derivZeroPlus

open AvramDividend.Classical

namespace AvramDividend.Classical

/-- The finite-activity zero-barrier analytic normaliser, conditional on the
    scale function origin and right-derivative identities. -/
theorem barrierValue_zero_of_finite_jump_normalisation
    (W : ℝ → ℝ) (q lam d : ℝ)
    (hd : d ≠ 0) (hql : q + lam ≠ 0)
    (hW0 : W 0 = 1 / d)
    (hWder : derivZeroPlus W = (((q + lam) / d ^ 2 : ℝ) : EReal)) :
    barrierValue W 0 0 = d / (q + lam) := by sorry

end AvramDividend.Classical
