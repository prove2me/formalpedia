-- Prove2me | Theorems.Thm_ActuarialValuation_siVar_nonneg
-- name    : ActuarialValuation.siVar_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:04:48.785703+00:00
-- url     : https://prove2.me/theorems/44549d8a-c435-4de7-8cef-2462df382e70
-- title:
--   Finite-scenario investment returns and fixed random rates: siVar_nonneg
-- statement:
--   Variance of a genuine normalized finite stochastic return law is nonnegative. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   S_n=(1+I)^n,\quad \mathbb{E}[S_n]=\sum_{\omega}p_{\omega}(1+I_{\omega})^n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 13. S. David Promislow, Fundamentals of Actuarial Mathematics (2015), Chapters on stochastic rates and annuity accumulation; Shreve (2004), Stochastic Calculus for Finance I, Chapter 1, https://link.springer.com/book/10.1007/978-0-387-22527-2. Parent topic: Finite-scenario expectation and variance; fixed random rate versus independent annual rates, product sample space and fund contribution moments. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://link.springer.com/book/10.1007/978-0-387-22527-2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siVar

namespace ActuarialValuation

theorem siVar_nonneg {m : ℕ} (p : Fin m → ℝ) (x : Fin m → ℝ) (hp : ∀ j, 0≤p j) (hs : (∑ j : Fin m, p j)=1) : 0≤siVar p x := by sorry

end ActuarialValuation
