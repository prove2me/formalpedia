-- Prove2me | Theorems.Thm_ActuarialValuation_kmRemainingRisk_balance
-- name    : ActuarialValuation.kmRemainingRisk_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:28:17.764373+00:00
-- url     : https://prove2.me/theorems/11a6c6c1-4266-4eda-8d54-b5f240748e1f
-- title:
--   Observed risk sets and interval exits: kmRemainingRisk_balance
-- statement:
--   At-risk conservation reconciles remaining lives, deaths and censoring. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   r_{t+1}+d_t+c_t=r_t
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmRemainingRisk
import Definitions.Def_actuarial_kmExitCount

namespace ActuarialValuation

theorem kmRemainingRisk_balance (r d c : ℝ) : kmRemainingRisk r d c + kmExitCount d c = r := by sorry

end ActuarialValuation
