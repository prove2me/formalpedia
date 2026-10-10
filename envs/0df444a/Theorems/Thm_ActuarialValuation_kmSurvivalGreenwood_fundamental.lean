-- Prove2me | Theorems.Thm_ActuarialValuation_kmSurvivalGreenwood_fundamental
-- name    : ActuarialValuation.kmSurvivalGreenwood_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:52:17.887238+00:00
-- url     : https://prove2.me/theorems/54264f03-f9f8-43ec-9c7d-674eb67152e0
-- title:
--   Greenwood uncertainty and finite restricted survival: kmSurvivalGreenwood_fundamental
-- statement:
--   The survival-estimation capstone proves the complete finite product-limit probability bounds, failure partition, nonnegative Greenwood plug-in variance and nonnegative restricted expected lifetime under strict risk-set conditions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   0\le S_{n+1}\le S_n,\;S_{n+1}+F_{n+1}=1,\;V_{n+1}\ge0,\;RMST_{n+1}\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmFailure
import Definitions.Def_actuarial_kmGreenwoodVariance
import Definitions.Def_actuarial_kmRestrictedLife

namespace ActuarialValuation

theorem kmSurvivalGreenwood_fundamental (risk deaths : ℕ → ℝ) (n : ℕ) (hr : ∀ t ∈ Finset.range (n+1), 0 < risk t) (hd : ∀ t ∈ Finset.range (n+1), 0 ≤ deaths t ∧ deaths t < risk t) : (0 ≤ kmSurvival risk deaths (n+1)) ∧ (kmSurvival risk deaths (n+1) ≤ kmSurvival risk deaths n) ∧ (kmSurvival risk deaths (n+1) + kmFailure risk deaths (n+1) = 1) ∧ (0 ≤ kmGreenwoodVariance risk deaths (n+1)) ∧ (0 ≤ kmRestrictedLife risk deaths (n+1)) := by sorry

end ActuarialValuation
