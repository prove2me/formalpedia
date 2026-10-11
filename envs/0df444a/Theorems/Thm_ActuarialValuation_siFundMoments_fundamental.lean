-- Prove2me | Theorems.Thm_ActuarialValuation_siFundMoments_fundamental
-- name    : ActuarialValuation.siFundMoments_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:11:17.274014+00:00
-- url     : https://prove2.me/theorems/c97c31d8-cf04-433e-b052-f1240bc5c258
-- title:
--   Regular contributions and fund first/second-moment recursions: siFundMoments_fundamental
-- statement:
--   The independent-return pension accumulation recursions reconcile first and second fund moments including contribution cross terms. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siFundMeanNext
import Definitions.Def_actuarial_siFundSecondNext
import Definitions.Def_actuarial_siFundVarianceNext

namespace ActuarialValuation

theorem siFundMoments_fundamental (v m c gross q : ℝ) (hv : m^2≤v) (hq : gross^2≤q) (hg : 0≤gross) : (siFundMeanNext m c gross=(m+c)*gross) ∧ (siFundSecondNext v m c q=(v+2*c*m+c^2)*q) ∧ (0≤siFundVarianceNext v m c gross q) := by sorry

end ActuarialValuation
