-- Prove2me | Theorems.Thm_ActuarialValuation_ipPoiRHS_one
-- name    : ActuarialValuation.ipPoiRHS_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:11:40.941742+00:00
-- url     : https://prove2.me/theorems/02f19fe3-1703-4c2f-8cb0-3f6c77e0cd24
-- title:
--   Full Poisson and geometric infinite Panjer recurrence: ipPoiRHS_one
-- statement:
--   First positive Poisson aggregate mass relation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipPoiRHS

namespace ActuarialValuation

theorem ipPoiRHS_one (l : ℝ) (f g : ℕ → ℝ) : ipPoiRHS l f g 1=l*f 1*g 0 := by sorry

end ActuarialValuation
