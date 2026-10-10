-- Prove2me | Theorems.Thm_ActuarialValuation_kmDeathHazard_nonneg
-- name    : ActuarialValuation.kmDeathHazard_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:13.412311+00:00
-- url     : https://prove2.me/theorems/d60d200a-b765-43fc-98cb-0dd74f4cee59
-- title:
--   Observed risk sets and interval exits: kmDeathHazard_nonneg
-- statement:
--   Positive risk denominator and nonnegative deaths imply nonnegative mortality fraction. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   d\ge0,r>0\Rightarrow q\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmDeathHazard

namespace ActuarialValuation

theorem kmDeathHazard_nonneg (d r : ℝ) (hd : 0 ≤ d) (hr : 0 < r) : 0 ≤ kmDeathHazard d r := by sorry

end ActuarialValuation
