-- Prove2me | Theorems.Thm_ActuarialValuation_siFundStep_zero_contribution
-- name    : ActuarialValuation.siFundStep_zero_contribution
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:08:42.153974+00:00
-- url     : https://prove2.me/theorems/ca1ae69b-1793-471b-b9ef-0276ff01b2ae
-- title:
--   Regular contributions and fund first/second-moment recursions: siFundStep_zero_contribution
-- statement:
--   Without a contribution the pension pot grows solely through investment. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   A_{n+1}=(A_n+c)G_{n+1},\quad m_{n+1}=(m_n+c)\bar G
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 13. S. David Promislow, Fundamentals of Actuarial Mathematics (2015), Chapters on stochastic rates and annuity accumulation; Shreve (2004), Stochastic Calculus for Finance I, Chapter 1, https://link.springer.com/book/10.1007/978-0-387-22527-2. Parent topic: Finite-scenario expectation and variance; fixed random rate versus independent annual rates, product sample space and fund contribution moments. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://link.springer.com/book/10.1007/978-0-387-22527-2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundStep

namespace ActuarialValuation

theorem siFundStep_zero_contribution (fund gross : ℝ) : siFundStep fund 0 gross=fund*gross := by sorry

end ActuarialValuation
