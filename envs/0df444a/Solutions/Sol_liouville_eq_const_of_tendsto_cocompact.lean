-- Prove2me | solution 1 for liouville_eq_const_of_tendsto_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-22T14:36:19.102317+00:00
-- url     : https://prove2.me/submissions/82d5aa1b-e7ca-4458-add3-a1d37f15217b

import Mathlib.Analysis.Complex.Polynomial.Basic

open Filter Topology


/-!
# Solution — `liouville_eq_const_of_tendsto_cocompact` (Liouville Child 2)

Direct proof: Mathlib's `Differentiable.apply_eq_of_tendsto_cocompact`, the
corollary of Liouville's theorem for functions with a finite limit at infinity.
-/

open Filter Topology

theorem solution {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {c : ℂ} (hgc : Tendsto g (cocompact ℂ) (𝓝 c)) (z : ℂ) : g z = c :=
  hg.apply_eq_of_tendsto_cocompact z hgc
