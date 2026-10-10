-- Prove2me | Theorems.Thm_ActuarialValuation_kmFailure_balance
-- name    : ActuarialValuation.kmFailure_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:41:11.839459+00:00
-- url     : https://prove2.me/theorems/9512b03a-a0e8-4a27-929a-37ac2c2b27af
-- title:
--   Kaplan-Meier product-limit survival: kmFailure_balance
-- statement:
--   The product-limit survival and failure estimates form complementary probabilities. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_n+F_n=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmFailure

namespace ActuarialValuation

theorem kmFailure_balance (r d : ℕ → ℝ) (n : ℕ) : kmSurvival r d n + kmFailure r d n = 1 := by sorry

end ActuarialValuation
