-- Prove2me | Theorems.Thm_ActuarialValuation_siMean_const
-- name    : ActuarialValuation.siMean_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:04:01.665995+00:00
-- url     : https://prove2.me/theorems/623ba331-1801-46c2-9a7c-ea87d4e544a7
-- title:
--   Finite-scenario investment returns and fixed random rates: siMean_const
-- statement:
--   A proper finite probability law has a constant-expectation identity. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem siMean_const {m : ℕ} (p : Fin m → ℝ) (c : ℝ) (h : (∑ j : Fin m, p j)=1) : siMean p (fun _ => c)=c := by sorry

end ActuarialValuation
