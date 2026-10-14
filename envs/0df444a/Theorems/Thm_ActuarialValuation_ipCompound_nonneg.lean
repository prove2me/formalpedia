-- Prove2me | Theorems.Thm_ActuarialValuation_ipCompound_nonneg
-- name    : ActuarialValuation.ipCompound_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:06:44.675864+00:00
-- url     : https://prove2.me/theorems/50a2f671-1a7f-4c3a-b7c5-ae1420150f24
-- title:
--   Countably infinite count laws and convolution powers: ipCompound_nonneg
-- statement:
--   True infinite aggregate mass is nonnegative. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipCompound

namespace ActuarialValuation

theorem ipCompound_nonneg (p f : ℕ → ℝ) (k : ℕ) (hp : ∀ j, 0≤p j) (hf : ∀ j, 0≤f j) : 0≤ ipCompound p f k := by sorry

end ActuarialValuation
