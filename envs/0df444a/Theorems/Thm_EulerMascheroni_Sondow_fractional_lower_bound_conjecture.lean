-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_fractional_lower_bound_conjecture
-- name    : EulerMascheroni.Sondow.fractional_lower_bound_conjecture
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:06:59.396652+00:00
-- url     : https://prove2.me/theorems/ebf8a88e-ef15-4154-8773-6ee4404e2d96
-- title:
--   Open Sondow fractional-part condition for Euler irrationality
-- statement:
--   Conjectural arithmetic condition: for every natural number $N$, there is an integer $n\ge\max(N,1)$ such that
--   $$\{d_{2n}L_n\}\ge2^{-n}.$$
--   Here $\{x\}=x-\lfloor x\rfloor$. This is the sufficient hypothesis of Sondow's Corollary 6, not a theorem proved in that paper. It is the unresolved arithmetic ingredient of this proposed route to irrationality; finite numerical evidence does not establish it.
-- source:
--   Jonathan Sondow, Criteria for Irrationality of Euler's Constant, https://arxiv.org/pdf/math/0209070 (v2, 4 October 2002). Corollary 6, p. 11; numerical discussion p. 4. Only the conditional implication is established by the source; the displayed infinite-occurrence assertion is an open conjectural target.

import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.fractional_lower_bound_conjecture :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      (1/2 : ℝ)^n ≤ Int.fract ((d (2*n) : ℝ) * L n) := by sorry
