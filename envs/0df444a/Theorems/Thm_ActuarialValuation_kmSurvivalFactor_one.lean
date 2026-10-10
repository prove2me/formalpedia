-- Prove2me | Theorems.Thm_ActuarialValuation_kmSurvivalFactor_one
-- name    : ActuarialValuation.kmSurvivalFactor_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:34:51.528493+00:00
-- url     : https://prove2.me/theorems/0bd1ab6c-662f-4df8-b764-ca63440c3109
-- title:
--   Kaplan-Meier product-limit survival: kmSurvivalFactor_one
-- statement:
--   A cohort entirely exhausted by deaths has zero further survival probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   r=d>0\Rightarrow p=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor

namespace ActuarialValuation

theorem kmSurvivalFactor_one (d : ℝ) (hd : d ≠ 0) : kmSurvivalFactor d d = 0 := by sorry

end ActuarialValuation
