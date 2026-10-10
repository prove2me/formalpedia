-- Prove2me | Theorems.Thm_ActuarialValuation_kmExitCount_zero
-- name    : ActuarialValuation.kmExitCount_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:26:07.999261+00:00
-- url     : https://prove2.me/theorems/361beeab-685c-4095-9de4-1ffeb1fc05e2
-- title:
--   Observed risk sets and interval exits: kmExitCount_zero
-- statement:
--   With no censoring, all risk-set departures are deaths. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e(d,0)=d
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmExitCount

namespace ActuarialValuation

theorem kmExitCount_zero (d : ℝ) : kmExitCount d 0 = d := by sorry

end ActuarialValuation
