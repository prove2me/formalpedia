-- Prove2me | Theorems.Thm_ActuarialValuation_ipFold_zero_atom
-- name    : ActuarialValuation.ipFold_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:03:52.418263+00:00
-- url     : https://prove2.me/theorems/9e1d453c-4abf-4c6f-8505-967ed4a1da0e
-- title:
--   Countably infinite count laws and convolution powers: ipFold_zero_atom
-- statement:
--   Probability of n all-zero claims is f0 to the n. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   p_n^{\mathrm{Poi}}=e^{-\lambda}\frac{\lambda^n}{n!}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results, https://doi.org/10.1017/S0515036100006802; Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 21. Parent topic: Poisson and geometric count laws, infinite frequency-severity convolution, analytic probability generating functions and corrected aggregate recursions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/abstract/recursive-evaluation-family-compound-distributions

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipFold

namespace ActuarialValuation

theorem ipFold_zero_atom (f : ℕ → ℝ) (n : ℕ) : ipFold f n 0=(f 0)^n := by sorry

end ActuarialValuation
