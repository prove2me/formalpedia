-- Prove2me | Theorems.Thm_ActuarialValuation_kmRemainingRisk_zero
-- name    : ActuarialValuation.kmRemainingRisk_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:28:07.599099+00:00
-- url     : https://prove2.me/theorems/3acf5bce-3a75-4328-a1f0-c1918930b87f
-- title:
--   Observed risk sets and interval exits: kmRemainingRisk_zero
-- statement:
--   No deaths or censoring leaves the risk count unchanged. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   r'=r\text{ if }d=c=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmRemainingRisk

namespace ActuarialValuation

theorem kmRemainingRisk_zero (r : ℝ) : kmRemainingRisk r 0 0 = r := by sorry

end ActuarialValuation
