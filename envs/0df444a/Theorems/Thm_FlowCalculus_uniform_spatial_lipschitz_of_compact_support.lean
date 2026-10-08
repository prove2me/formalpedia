-- Prove2me | Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
-- name    : FlowCalculus.uniform_spatial_lipschitz_of_compact_support
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:22:24.312903+00:00
-- url     : https://prove2.me/theorems/fdc40129-b9a9-47f0-9271-d44b599a30cb
-- title:
--   Uniform spatial Lipschitz bound for a smooth uniformly compact-supported field
-- statement:
--   Let V be a real normed vector space and X:ℝ×V→V a smooth vector field. Suppose one compact set K contains the support of X(t,·) for every real time t. For every closed bounded time interval [a,b], there is a nonnegative constant L such that
--
--   $$ \|X(t,y)-X(t,z)\| \le L\|y-z\| \qquad(t\in[a,b],\ y,z\in V). $$
--
--   The bound holds uniformly over all spatial points. No completeness or finite-dimensionality of V is required. This uniform Lipschitz control supplies the uniqueness and Picard–Lindelöf hypotheses for complete trajectories.
-- source:
--   Auxiliary completeness argument for Gray stability (Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed p. 15). The proof uses compactness of [a,b]×K and the mean value inequality, Mathlib.Analysis.Calculus.MeanValue.lipschitzWith_of_nnnorm_fderiv_le at commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Congr

open Set
open scoped ContDiff Topology NNReal

theorem FlowCalculus.uniform_spatial_lipschitz_of_compact_support {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (a b : ℝ) : ∃ L : ℝ≥0, ∀ t ∈ Icc a b, LipschitzWith L (X t) := by sorry
