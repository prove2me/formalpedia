-- Prove2me | Theorems.Thm_ActuarialValuation_ipTail_monotone
-- name    : ActuarialValuation.ipTail_monotone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:19:00.3587+00:00
-- url     : https://prove2.me/theorems/a9eead60-e56a-4abc-8fb1-a29a5c3426fb
-- title:
--   Full Poisson and geometric infinite Panjer recurrence: ipTail_monotone
-- statement:
--   Higher solvency capital reduces exceedance. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipTail

namespace ActuarialValuation

theorem ipTail_monotone (p f : ℕ → ℝ) (k : ℕ) (hp : ∀ n, 0≤p n) (hf : ∀ n, 0≤f n) : ipTail p f (k+1)≤ ipTail p f k := by sorry

end ActuarialValuation
