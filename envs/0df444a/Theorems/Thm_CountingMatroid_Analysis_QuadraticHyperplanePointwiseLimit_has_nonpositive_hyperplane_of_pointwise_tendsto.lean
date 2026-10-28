-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_QuadraticHyperplanePointwiseLimit_has_nonpositive_hyperplane_of_pointwise_tendsto
-- name    : CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit.has_nonpositive_hyperplane_of_pointwise_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:28:02.599011+00:00
-- url     : https://prove2.me/theorems/6c6b772b-34d3-4202-ac80-8f80d8b3d7bc
-- title:
--   Nonpositive hyperplanes are preserved by pointwise limits
-- statement:
--   Let $V$ be a real vector space, let $(Q_n)_{n\in\mathbb N}$ and $Q$ be real quadratic forms on $V$, and suppose every $Q_n$ has a nonpositive hyperplane. Say that a real quadratic form has a nonpositive hyperplane if there is a linear functional $\ell$ such that $\ell(v)=0$ implies $Q(v)\le0$. The functional may be zero, so the kernel has codimension at most one. Assume $$\forall v\in V,\qquad Q_n(v)\longrightarrow Q(v).$$ Then $$\exists\ell:V\to\mathbb R\text{ linear},\qquad \ell(v)=0\Longrightarrow Q(v)\le0.$$ No finite-dimensional or topological structure on $V$ is assumed.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/QuadraticHyperplanePointwiseLimit.lean#L19-L69

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
set_option autoImplicit false

/-!
Pointwise limits of real quadratic forms preserve a nonpositive hyperplane,
without a dimension hypothesis. A positive vector of the limit fixes its
associated kernel; polynomially corrected vectors in the approximants give
the limiting inequality on that kernel.
-/

namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit

open Filter
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit.has_nonpositive_hyperplane_of_pointwise_tendsto {V : Type}
    [AddCommGroup V] [Module ℝ V] [Invertible (2 : ℝ)]
    (Qn : ℕ → QuadraticForm ℝ V) (Q : QuadraticForm ℝ V)
    (hn : ∀ n, HasNonpositiveHyperplane (Qn n))
    (hconv : ∀ v, Tendsto (fun n => Qn n v) atTop (nhds (Q v))) :
    HasNonpositiveHyperplane Q := by sorry
