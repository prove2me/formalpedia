-- Prove2me | Theorems.Thm_ActuarialValuation_ipPoisson_Panjer
-- name    : ActuarialValuation.ipPoisson_Panjer
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:19:32.450694+00:00
-- url     : https://prove2.me/theorems/c4c80689-1127-4ac5-a736-1c5a62256c74
-- title:
--   Full Poisson and geometric infinite Panjer recurrence: ipPoisson_Panjer
-- statement:
--   Derive Poisson severity-weighted recurrence from actual infinite random sum. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipPoisson
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipPoiRHS

namespace ActuarialValuation

theorem ipPoisson_Panjer (l : ℝ) (f : ℕ → ℝ) (k : ℕ) (hl : 0≤l) (hf : ∀ n, 0≤f n) (hs : (∑' n : ℕ, f n)=1) (hk : 0<k) : ipCompound (ipPoisson l) f k=ipPoiRHS l f (ipCompound (ipPoisson l) f) k := by sorry

end ActuarialValuation
