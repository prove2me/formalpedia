-- Prove2me | Theorems.Thm_ContinuousMapCalculus_contDiff_postcomp
-- name    : ContinuousMapCalculus.contDiff_postcomp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:18:08.694399+00:00
-- url     : https://prove2.me/theorems/b8bc7228-76dc-4d83-b998-bfd63d9d0a16
-- title:
--   Smooth postcomposition on continuous maps from a compact space
-- statement:
--   Let K be a compact topological space and E,F real normed spaces. If f:E→F is smooth, then its postcomposition map between spaces of continuous functions is smooth in the supremum norm:
--
--   $$ C(K,E)\longrightarrow C(K,F),\qquad \gamma\longmapsto f\circ\gamma. $$
--
--   Neither finite dimensionality nor completeness is assumed. This result allows nonlinear pointwise operations to be differentiated in spaces of continuous curves.
-- source:
--   Original compact-domain superposition lemma for smooth ODE dependence. Proof by induction using the Fréchet mean-value inequality in Mathlib.Analysis.Calculus.MeanValue and the derivative characterization in Mathlib.Analysis.Calculus.ContDiff.Defs; pinned sources https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus. This supplies the function-space smoothness used in the Picard integral formulation of Teschl, Ordinary Differential Equations and Dynamical Systems, §2.4, Theorem 2.10.

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
open Set Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

theorem ContinuousMapCalculus.contDiff_postcomp {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun γ : C(K,E) => (⟨f,hf.continuous⟩ : C(E,F)).comp γ) := by sorry
