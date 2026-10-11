-- Prove2me | Theorems.Thm_ActuarialValuation_ipPoint_zero
-- name    : ActuarialValuation.ipPoint_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:00:19.782857+00:00
-- url     : https://prove2.me/theorems/a3accbfa-5874-43ea-871c-d6a5a2a4eb83
-- title:
--   Countably infinite count laws and convolution powers: ipPoint_zero
-- statement:
--   No-claim aggregate zero atom is one. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipPoint

namespace ActuarialValuation

theorem ipPoint_zero  : ipPoint 0=1 := by sorry

end ActuarialValuation
