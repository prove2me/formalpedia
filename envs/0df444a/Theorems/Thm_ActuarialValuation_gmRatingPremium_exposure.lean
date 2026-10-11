-- Prove2me | Theorems.Thm_ActuarialValuation_gmRatingPremium_exposure
-- name    : ActuarialValuation.gmRatingPremium_exposure
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:12:09.899526+00:00
-- url     : https://prove2.me/theorems/f00d3fa3-eb18-49ec-91c7-ee9837ee7599
-- title:
--   Claims deviance, premium relativity and model comparison: gmRatingPremium_exposure
-- statement:
--   Total expected losses equal exposure times the per-unit risk premium. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   D_{\text{Poi}}=2\left[y\log\left(\frac{y}{\mu}\right)-(y-\mu)\right]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 373. J. A. Nelder and R. W. M. Wedderburn (1972), Generalized Linear Models, JRSS A 135:370–384, https://doi.org/10.2307/2344614; actuarial practice in casualty generalized linear models https://www.casact.org/sites/default/files/2021-03/05-Goldburd-Khare-Tevet.pdf. Parent topic: Positive insurance exposure offsets, Poisson log-link likelihood and score, Fisher information, deviance and multiplicative premium relativities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/2344614

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmRate
import Definitions.Def_actuarial_gmPurePremium
import Definitions.Def_actuarial_gmRatingPremium

namespace ActuarialValuation

theorem gmRatingPremium_exposure (exposure eta severity : ℝ) : gmRatingPremium exposure eta severity=exposure*gmPurePremium (gmRate eta) severity := by sorry

end ActuarialValuation
