-- Prove2me | Theorems.Thm_BCWCentralizer_theoremA_wandering
-- name    : BCWCentralizer.theoremA_wandering
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:27:08.128607+00:00
-- url     : https://prove2.me/theorems/a03f6c55-8cc1-48d8-983e-d0a504f33c70
-- title:
--   Theorem A (wandering part): unbounded distortion on the wandering set is $C^1$-generic
-- statement:
--   Let $M$ be a closed connected smooth manifold of dimension $d$, equipped with a continuous Riemannian metric. The set of $f\in\mathrm{Diff}^1(M)$ satisfying the unbounded distortion property on the wandering set $(UD_{M\setminus\Omega})$ is residual in $\mathrm{Diff}^1(M)$ for the $C^1$ topology. Recall that $(UD_{M\setminus\Omega})$ asks for a subset $\mathcal X$, dense in $M\setminus\Omega(f)$, such that for any $K>0$, $x\in\mathcal X$ and $y\in M\setminus\Omega(f)$ not on the orbit of $x$, there is $n\ge1$ with
--   $$\big|\log|\det Df^n(x)|-\log|\det Df^n(y)|\big|>K.$$
--
--   Theorem A of the paper asserts that the properties $(UD_{M\setminus\Omega})$ and $(UD^s)$ hold on a residual set; the $(UD^s)$ part follows from earlier work of Togawa and the authors, and the paper states that it remains to prove that $(UD_{M\setminus\Omega})$ holds for a $C^1$-generic diffeomorphism. This milestone is that remaining statement.
-- source:
--   Bonatti, Crovisier, Wilkinson, *The C^1 generic diffeomorphism has trivial centralizer*, arXiv:0804.1416v1 (2008), https://arxiv.org/abs/0804.1416, p. 12, Theorem A and the paragraph following it (the $(UD_{M\setminus\Omega})$ half)

import Mathlib
import Definitions.Def_BCWCentralizer_Basic
import Definitions.Def_BCWCentralizer_Dynamics

open scoped Manifold ContDiff Topology
open Bundle

namespace BCWCentralizer
theorem theoremA_wandering {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 d) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin d)) (fun x : M ↦ TangentSpace (𝓡 d) x)] :
    {f : Diff1 d M | HasUDWandering f} ∈ residual (Diff1 d M) := by sorry
end BCWCentralizer
