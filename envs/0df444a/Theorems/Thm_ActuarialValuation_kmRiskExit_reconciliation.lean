-- Prove2me | Theorems.Thm_ActuarialValuation_kmRiskExit_reconciliation
-- name    : ActuarialValuation.kmRiskExit_reconciliation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:51.386006+00:00
-- url     : https://prove2.me/theorems/6a7a577f-9f58-4f63-bd3f-e36ab5b835af
-- title:
--   Observed risk sets and interval exits: kmRiskExit_reconciliation
-- statement:
--   Death and censoring hazards sum to the total observed exit fraction, without equating censoring to mortality. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   d/r+c/r=(d+c)/r
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmExitCount
import Definitions.Def_actuarial_kmDeathHazard
import Definitions.Def_actuarial_kmCensorHazard

namespace ActuarialValuation

theorem kmRiskExit_reconciliation (r d c : ℝ) (hr : r ≠ 0) : kmDeathHazard d r + kmCensorHazard c r = kmExitCount d c / r := by sorry

end ActuarialValuation
