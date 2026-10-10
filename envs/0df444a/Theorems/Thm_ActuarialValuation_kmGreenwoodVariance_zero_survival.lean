-- Prove2me | Theorems.Thm_ActuarialValuation_kmGreenwoodVariance_zero_survival
-- name    : ActuarialValuation.kmGreenwoodVariance_zero_survival
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:51:10.549965+00:00
-- url     : https://prove2.me/theorems/16509a0c-4ab1-485b-962e-058ac2727743
-- title:
--   Greenwood uncertainty and finite restricted survival: kmGreenwoodVariance_zero_survival
-- statement:
--   The finite plug-in variance expression vanishes if its product-limit survival factor is zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_n=0\Rightarrow V_n=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmGreenwoodVariance

namespace ActuarialValuation

theorem kmGreenwoodVariance_zero_survival (r d : ℕ → ℝ) (n : ℕ) (h : kmSurvival r d n = 0) : kmGreenwoodVariance r d n = 0 := by sorry

end ActuarialValuation
