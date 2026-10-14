-- Prove2me | Theorems.Thm_ActuarialValuation_ipPoi_zero_atom
-- name    : ActuarialValuation.ipPoi_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:11:07.000983+00:00
-- url     : https://prove2.me/theorems/60d49aff-014b-4f31-a2d5-0da09973952c
-- title:
--   Probability generating functions, mass normalisation and zero atoms: ipPoi_zero_atom
-- statement:
--   Compound Poisson zero mass comes from thinning. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   g_k=\sum_{n=0}^{\infty}p_n(f^{*n})_k,\quad g_0=G_N(f_0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results, https://doi.org/10.1017/S0515036100006802; Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 21. Parent topic: Poisson and geometric count laws, infinite frequency-severity convolution, analytic probability generating functions and corrected aggregate recursions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/abstract/recursive-evaluation-family-compound-distributions

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoisson
import Definitions.Def_actuarial_ipCompound

namespace ActuarialValuation

theorem ipPoi_zero_atom (l : ℝ) (f : ℕ → ℝ) (hf0 : 0≤f 0) (hf1 : f 0≤1) : ipCompound (ipPoisson l) f 0=Real.exp (-l*(1-f 0)) := by sorry

end ActuarialValuation
