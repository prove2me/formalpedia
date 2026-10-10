-- Prove2me | Theorems.Thm_ActuarialValuation_kmSurvival_le_one
-- name    : ActuarialValuation.kmSurvival_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:38:33.108065+00:00
-- url     : https://prove2.me/theorems/de151db3-279a-46dd-90f5-184771899488
-- title:
--   Kaplan-Meier product-limit survival: kmSurvival_le_one
-- statement:
--   Multiplying valid conditional survival fractions cannot raise total survival above one. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   0\le p_t\le1\Rightarrow S_n\le1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor
import Definitions.Def_actuarial_kmSurvival

namespace ActuarialValuation

theorem kmSurvival_le_one (r d : ℕ → ℝ) (n : ℕ) (h : ∀ t ∈ Finset.range n, 0 ≤ kmSurvivalFactor (d t) (r t) ∧ kmSurvivalFactor (d t) (r t) ≤ 1) : kmSurvival r d n ≤ 1 := by sorry

end ActuarialValuation
