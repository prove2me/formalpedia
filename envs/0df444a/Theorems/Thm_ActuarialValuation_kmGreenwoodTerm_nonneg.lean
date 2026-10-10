-- Prove2me | Theorems.Thm_ActuarialValuation_kmGreenwoodTerm_nonneg
-- name    : ActuarialValuation.kmGreenwoodTerm_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:46:42.510944+00:00
-- url     : https://prove2.me/theorems/b726fd31-2927-4129-ace2-7464b21cab16
-- title:
--   Greenwood uncertainty and finite restricted survival: kmGreenwoodTerm_nonneg
-- statement:
--   Positive remaining risk guarantees a nonnegative Greenwood contribution. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   0\le d<r\Rightarrow g\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodTerm

namespace ActuarialValuation

theorem kmGreenwoodTerm_nonneg (d r : ℝ) (hd : 0 ≤ d) (hr : d < r) : 0 ≤ kmGreenwoodTerm d r := by sorry

end ActuarialValuation
