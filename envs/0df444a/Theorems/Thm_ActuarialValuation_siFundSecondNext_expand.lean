-- Prove2me | Theorems.Thm_ActuarialValuation_siFundSecondNext_expand
-- name    : ActuarialValuation.siFundSecondNext_expand
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:10:08.302295+00:00
-- url     : https://prove2.me/theorems/bd8a5540-8e19-41ac-aac8-ab950bf22e80
-- title:
--   Regular contributions and fund first/second-moment recursions: siFundSecondNext_expand
-- statement:
--   Fund second-moment recursion includes contribution cross terms. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siFundSecondNext

namespace ActuarialValuation

theorem siFundSecondNext_expand (v m c q : ℝ) : siFundSecondNext v m c q=(v+2*c*m+c^2)*q := by sorry

end ActuarialValuation
