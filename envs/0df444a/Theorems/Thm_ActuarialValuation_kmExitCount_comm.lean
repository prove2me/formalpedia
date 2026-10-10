-- Prove2me | Theorems.Thm_ActuarialValuation_kmExitCount_comm
-- name    : ActuarialValuation.kmExitCount_comm
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:27:21.237574+00:00
-- url     : https://prove2.me/theorems/7453e57f-e2a0-47ac-8b63-292b2789618e
-- title:
--   Observed risk sets and interval exits: kmExitCount_comm
-- statement:
--   The total number of exits does not depend on the order in which disjoint categories are added. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   d+c=c+d
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmExitCount

namespace ActuarialValuation

theorem kmExitCount_comm (d c : ℝ) : kmExitCount d c = kmExitCount c d := by sorry

end ActuarialValuation
