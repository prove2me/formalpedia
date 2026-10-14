-- Prove2me | Theorems.Thm_ActuarialValuation_siFundVarianceNext_zero
-- name    : ActuarialValuation.siFundVarianceNext_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:10:33.588344+00:00
-- url     : https://prove2.me/theorems/28e9401f-f45d-460f-a54b-c21ee3822d98
-- title:
--   Regular contributions and fund first/second-moment recursions: siFundVarianceNext_zero
-- statement:
--   With deterministic prior fund and deterministic next-year return no variance remains. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siFundVarianceNext

namespace ActuarialValuation

theorem siFundVarianceNext_zero (v m c gross secondGross : ℝ) (hv : v=m^2) (hq : secondGross=gross^2) : siFundVarianceNext v m c gross secondGross=0 := by sorry

end ActuarialValuation
