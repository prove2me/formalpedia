-- Prove2me | Theorems.Thm_ActuarialValuation_siMean_add
-- name    : ActuarialValuation.siMean_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:03:47.551859+00:00
-- url     : https://prove2.me/theorems/c70faf0f-f063-4aba-87d7-5229c3244056
-- title:
--   Finite-scenario investment returns and fixed random rates: siMean_add
-- statement:
--   Actuarial finite-scenario means are linear. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siMean

namespace ActuarialValuation

theorem siMean_add {m : ℕ} (p : Fin m → ℝ) (x y : Fin m → ℝ) : siMean p (fun j => x j+y j)=siMean p x+siMean p y := by sorry

end ActuarialValuation
