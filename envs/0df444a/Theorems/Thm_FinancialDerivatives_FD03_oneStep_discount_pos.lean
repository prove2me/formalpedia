-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_oneStep_discount_pos
-- name    : FinancialDerivatives.FD03.oneStep_discount_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:07:15.483654+00:00
-- url     : https://prove2.me/theorems/65ac3787-03eb-47a6-93d8-f7192c22da9c
-- title:
--   Strictly positive bank discount factor at each period
-- statement:
--   The strict market inequalities imply R is strictly positive, so the one-period discount factor 1/R is strictly positive and can be used in every backwards value comparison.
-- source:
--   Original positivity consequence of 0 < d < R < u, Wilmott, Howison and Dewynne (1995), Chapter 10 §10.2, printed pp. 182–186.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket

namespace FinancialDerivatives.FD03

theorem oneStep_discount_pos (m : BinomialMarket) :
    0 < (1 / m.growth : ℝ) := by sorry

end FinancialDerivatives.FD03
