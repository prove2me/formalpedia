-- Prove2me | Theorems.Thm_ActuarialValuation_kmRestrictedLife_succ
-- name    : ActuarialValuation.kmRestrictedLife_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:51:48.888409+00:00
-- url     : https://prove2.me/theorems/fb4fd9b8-979e-4bb0-aef1-acedd34f57d7
-- title:
--   Greenwood uncertainty and finite restricted survival: kmRestrictedLife_succ
-- statement:
--   A new discrete duration interval contributes its initial survival probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   RMST_{n+1}=RMST_n+S_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmRestrictedLife

namespace ActuarialValuation

theorem kmRestrictedLife_succ (r d : ℕ → ℝ) (n : ℕ) : kmRestrictedLife r d (n+1) = kmRestrictedLife r d n + kmSurvival r d n := by sorry

end ActuarialValuation
