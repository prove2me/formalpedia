-- Prove2me | Theorems.Thm_ActuarialValuation_gmPurePremium_zero
-- name    : ActuarialValuation.gmPurePremium_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:03:55.317056+00:00
-- url     : https://prove2.me/theorems/2c548e08-5f20-42fc-921e-baea006e7666
-- title:
--   Positive claim rates, log links and exposure offsets: gmPurePremium_zero
-- statement:
--   No claims means no expected loss. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \mu=E e^\eta,\quad \log \mu=\log E+\eta
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 373. J. A. Nelder and R. W. M. Wedderburn (1972), Generalized Linear Models, JRSS A 135:370–384, https://doi.org/10.2307/2344614; actuarial practice in casualty generalized linear models https://www.casact.org/sites/default/files/2021-03/05-Goldburd-Khare-Tevet.pdf. Parent topic: Positive insurance exposure offsets, Poisson log-link likelihood and score, Fisher information, deviance and multiplicative premium relativities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/2344614

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmPurePremium

namespace ActuarialValuation

theorem gmPurePremium_zero (severity : ℝ) : gmPurePremium 0 severity=0 := by sorry

end ActuarialValuation
