-- Prove2me | Theorems.Thm_ActuarialValuation_ipGeoRHS_one
-- name    : ActuarialValuation.ipGeoRHS_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:11:25.946752+00:00
-- url     : https://prove2.me/theorems/c7c793a3-103e-45e8-b71b-8f9c60bd0ba2
-- title:
--   Full Poisson and geometric infinite Panjer recurrence: ipGeoRHS_one
-- statement:
--   First positive geometric aggregate mass relation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   (1-qf_0)g_k=q\sum_{j=1}^kf_jg_{k-j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results, https://doi.org/10.1017/S0515036100006802; Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 21. Parent topic: Poisson and geometric count laws, infinite frequency-severity convolution, analytic probability generating functions and corrected aggregate recursions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/abstract/recursive-evaluation-family-compound-distributions

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipGeoRHS

namespace ActuarialValuation

theorem ipGeoRHS_one (q : ℝ) (f g : ℕ → ℝ) : ipGeoRHS q f g 1=q*f 1*g 0 := by sorry

end ActuarialValuation
