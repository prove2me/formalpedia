-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_NonnegativeContractionLimit_nonnegative_contraction_limit
-- name    : CountingMatroid.Analysis.NonnegativeContractionLimit.nonnegative_contraction_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:53:15.264333+00:00
-- url     : https://prove2.me/theorems/bf5aac62-d772-4e9e-829a-e8a2f074e028
-- title:
--   Nonnegative contractions are limits of strictly positive contractions
-- statement:
--   Let $\sigma$ be a finite set, let $V$ be any real vector space, and let $(Q_s)_{s\in\sigma}$ be real quadratic forms on $V$. Suppose that for every rational vector $a$ with $a_s>0$ for all $s$, there is a real linear functional $f_a$ such that $$f_a(v)=0\ \Longrightarrow\ \sum_s a_sQ_s(v)\le0.$$ Then for every rational vector $d$ with $d_s\ge0$, there is a real linear functional $f$ satisfying $$f(v)=0\ \Longrightarrow\ \sum_s d_sQ_s(v)\le0.$$ Zero functionals are permitted, and $V$ need not be finite dimensional.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/NonnegativeContractionLimit.lean#L20-L49

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
set_option autoImplicit false

/-!
The boundary step for finite rationally weighted sums of real quadratic forms.
Strictly positive weights approximate nonnegative weights. Pointwise closure
of the nonpositive-hyperplane property gives the boundary case, without any
finite-dimensionality or tensor hypotheses.
-/

namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.NonnegativeContractionLimit

open scoped BigOperators
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.NonnegativeContractionLimit.nonnegative_contraction_limit {σ V : Type} [Fintype σ]
    [AddCommGroup V] [Module ℝ V] [Invertible (2 : ℝ)]
    (Q : σ → QuadraticForm ℝ V)
    (hpositive : ∀ d : σ → ℚ, (∀ s, 0 < d s) →
      HasNonpositiveHyperplane (∑ s, (d s : ℝ) • Q s))
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    HasNonpositiveHyperplane (∑ s, (d s : ℝ) • Q s) := by sorry
