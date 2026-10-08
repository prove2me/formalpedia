-- Prove2me | Theorems.Thm_ContinuousMapCalculus_hasFDerivAt_of_pointwise
-- name    : ContinuousMapCalculus.hasFDerivAt_of_pointwise
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:07:14.728029+00:00
-- url     : https://prove2.me/theorems/27217ec6-ca80-49c3-86ac-4d1439f0b370
-- title:
--   Pointwise derivatives lift to the supremum norm
-- statement:
--   Let K be a compact topological space and E,F real normed spaces. Equip C(K,F) with the supremum norm. Suppose f:E→C(K,F) and g:E→L(E,C(K,F)), and fix x∈E. Assume g is continuous at x in operator norm and every coordinate z↦f(z)(k) is differentiable at every y, with derivative v↦g(y)(v)(k). Then
--
--   $$ Df(x)=g(x). $$
--
--   This transfers a coordinate derivative calculation to a Fréchet derivative in the space of continuous functions. Completeness and finite dimensionality are not required.
-- source:
--   Original compact-domain calculus lemma for the function-space proof of smooth ODE dependence. Derived from Mathlib Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le', https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/MeanValue.lean, and ContinuousMap.norm_le (supremum norm).

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

open Set Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem ContinuousMapCalculus.hasFDerivAt_of_pointwise {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → C(K,F)) (g : E → E →L[ℝ] C(K,F)) (x : E)
    (hg : ContinuousAt g x)
    (hd : ∀ y k, HasFDerivAt (fun z => f z k)
      ((ContinuousMap.evalCLM ℝ k).comp (g y)) y) :
    HasFDerivAt f (g x) x := by sorry
