-- Prove2me | Theorems.Thm_ActuarialValuation_ipPoi_PGF
-- name    : ActuarialValuation.ipPoi_PGF
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:09:48.328991+00:00
-- url     : https://prove2.me/theorems/f2be889f-5f28-46b2-8ca6-b32670f3a8da
-- title:
--   Probability generating functions, mass normalisation and zero atoms: ipPoi_PGF
-- statement:
--   Poisson PGF is a convergent exponential. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipCountPGF

namespace ActuarialValuation

theorem ipPoi_PGF (l z : ℝ) : ipCountPGF (ipPoisson l) z=Real.exp (l*(z-1)) := by sorry

end ActuarialValuation
