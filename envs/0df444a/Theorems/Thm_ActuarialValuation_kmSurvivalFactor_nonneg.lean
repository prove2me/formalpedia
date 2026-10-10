-- Prove2me | Theorems.Thm_ActuarialValuation_kmSurvivalFactor_nonneg
-- name    : ActuarialValuation.kmSurvivalFactor_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:04.23243+00:00
-- url     : https://prove2.me/theorems/16f9f8c5-728f-4693-9122-d0991a481976
-- title:
--   Kaplan-Meier product-limit survival: kmSurvivalFactor_nonneg
-- statement:
--   Observed interval survival is nonnegative for a valid death fraction. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   d\le r,r>0\Rightarrow p\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor

namespace ActuarialValuation

theorem kmSurvivalFactor_nonneg (d r : ℝ) (h : d ≤ r) (hr : 0 < r) : 0 ≤ kmSurvivalFactor d r := by sorry

end ActuarialValuation
