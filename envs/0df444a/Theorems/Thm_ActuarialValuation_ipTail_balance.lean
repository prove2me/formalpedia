-- Prove2me | Theorems.Thm_ActuarialValuation_ipTail_balance
-- name    : ActuarialValuation.ipTail_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:18:36.892275+00:00
-- url     : https://prove2.me/theorems/15190e45-f5b5-42db-b53e-f946e40da41f
-- title:
--   Full Poisson and geometric infinite Panjer recurrence: ipTail_balance
-- statement:
--   Aggregate tail and cumulative probability sum to one. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipCDF
import Definitions.Def_actuarial_ipTail

namespace ActuarialValuation

theorem ipTail_balance (p f : ℕ → ℝ) (k : ℕ) : ipTail p f k+ipCDF p f k=1 := by sorry

end ActuarialValuation
