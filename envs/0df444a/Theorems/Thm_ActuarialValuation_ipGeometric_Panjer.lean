-- Prove2me | Theorems.Thm_ActuarialValuation_ipGeometric_Panjer
-- name    : ActuarialValuation.ipGeometric_Panjer
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:19:16.864277+00:00
-- url     : https://prove2.me/theorems/438b404a-0b5e-4bf4-80f9-88973b298aa3
-- title:
--   Full Poisson and geometric infinite Panjer recurrence: ipGeometric_Panjer
-- statement:
--   Derive all positive geometric aggregate masses from actual infinite random sum. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipGeo
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipGeoRHS

namespace ActuarialValuation

theorem ipGeometric_Panjer (q : ℝ) (f : ℕ → ℝ) (k : ℕ) (hq0 : 0≤q) (hq1 : q<1) (hf : ∀ n, 0≤f n) (hs : (∑' n : ℕ, f n)=1) (hk : 0<k) : (1-q*f 0)*ipCompound (ipGeo q) f k=ipGeoRHS q f (ipCompound (ipGeo q) f) k := by sorry

end ActuarialValuation
