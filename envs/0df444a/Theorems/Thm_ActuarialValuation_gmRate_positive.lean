-- Prove2me | Theorems.Thm_ActuarialValuation_gmRate_positive
-- name    : ActuarialValuation.gmRate_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:00:48.984987+00:00
-- url     : https://prove2.me/theorems/9263f5d8-c4bc-4080-be62-b85884fe9dce
-- title:
--   Positive claim rates, log links and exposure offsets: gmRate_positive
-- statement:
--   Log-link predicted claim frequency is always positive. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_gmRate

namespace ActuarialValuation

theorem gmRate_positive (eta : ℝ) : 0<gmRate eta := by sorry

end ActuarialValuation
