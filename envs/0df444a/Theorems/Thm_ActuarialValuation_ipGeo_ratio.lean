-- Prove2me | Theorems.Thm_ActuarialValuation_ipGeo_ratio
-- name    : ActuarialValuation.ipGeo_ratio
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:05:37.004418+00:00
-- url     : https://prove2.me/theorems/bdcb5217-78ef-4fab-98d0-b45beb83f5a0
-- title:
--   Countably infinite count laws and convolution powers: ipGeo_ratio
-- statement:
--   Geometric count frequency ratio. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipGeo

namespace ActuarialValuation

theorem ipGeo_ratio (q : ℝ) (n : ℕ) : ipGeo q (n+1)=q*ipGeo q n := by sorry

end ActuarialValuation
