-- Prove2me | Theorems.Thm_ActuarialValuation_kmSurvival_succ
-- name    : ActuarialValuation.kmSurvival_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:45.645988+00:00
-- url     : https://prove2.me/theorems/37a5a97c-89c7-4648-a82a-c78350f675e8
-- title:
--   Kaplan-Meier product-limit survival: kmSurvival_succ
-- statement:
--   The Kaplan-Meier survival product updates only at the next event time. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_{n+1}=S_np_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor
import Definitions.Def_actuarial_kmSurvival

namespace ActuarialValuation

theorem kmSurvival_succ (r d : ℕ → ℝ) (n : ℕ) : kmSurvival r d (n+1) = kmSurvival r d n * kmSurvivalFactor (d n) (r n) := by sorry

end ActuarialValuation
