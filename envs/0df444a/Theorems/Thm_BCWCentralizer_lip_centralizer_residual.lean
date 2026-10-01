-- Prove2me | Theorems.Thm_BCWCentralizer_lip_centralizer_residual
-- name    : BCWCentralizer.lip_centralizer_residual
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:35:44.294069+00:00
-- url     : https://prove2.me/theorems/7b86684b-2a76-496b-9b83-3821b0599867
-- title:
--   Theorem 2.3: trivial Lipschitz centralizer is $C^1$-generic when $\dim M\ge2$
-- statement:
--   Let $M$ be a closed connected smooth manifold of dimension $d\ge2$. The set of $f\in\mathrm{Diff}^1(M)$ whose Lipschitz centralizer is trivial,
--   $$Z^{\mathrm{Lip}}(f)=\{g\in\mathrm{Lip}(M): fg=gf\}=\{f^n:n\in\mathbb Z\},$$
--   is residual in $\mathrm{Diff}^1(M)$ for the $C^1$ topology. Here $\mathrm{Lip}(M)$ is the group of bi-Lipschitz homeomorphisms of $M$.
--
--   Since $\mathrm{Diff}^1(M)\subset\mathrm{Lip}(M)$, this implies the Main Theorem in dimension at least $2$.
-- source:
--   Bonatti, Crovisier, Wilkinson, *The C^1 generic diffeomorphism has trivial centralizer*, arXiv:0804.1416v1 (2008), https://arxiv.org/abs/0804.1416, p. 15, Theorem 2.3

import Mathlib
import Definitions.Def_BCWCentralizer_Basic

open scoped Manifold ContDiff Topology

namespace BCWCentralizer
theorem lip_centralizer_residual {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (hd : 2 ≤ d) :
    {f : Diff1 d M | HasTrivialLipCentralizer f} ∈ residual (Diff1 d M) := by sorry
end BCWCentralizer
