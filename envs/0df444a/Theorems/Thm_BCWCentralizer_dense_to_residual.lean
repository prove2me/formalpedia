-- Prove2me | Theorems.Thm_BCWCentralizer_dense_to_residual
-- name    : BCWCentralizer.dense_to_residual
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:34:05.988983+00:00
-- url     : https://prove2.me/theorems/8bdf021c-e3c9-4fe5-ade4-0251409a9054
-- title:
--   Proposition 2.5: dense trivial Lipschitz centralizers are residual
-- statement:
--   Let $M$ be a closed connected smooth manifold of dimension $d$ and let
--   $$\mathcal T=\{f\in\mathrm{Diff}^1(M):\ Z^{\mathrm{Lip}}(f)=\langle f\rangle\}$$
--   be the set of $C^1$ diffeomorphisms whose Lipschitz centralizer is trivial, i.e. every bi-Lipschitz homeomorphism $g$ with $fg=gf$ is a power $f^n$, $n\in\mathbb Z$. If $\mathcal T$ is dense in $\mathrm{Diff}^1(M)$ (with the $C^1$ topology), then $\mathcal T$ is residual.
--
--   This is the "dense to residual" half of the proof of Theorem 2.3.
-- source:
--   Bonatti, Crovisier, Wilkinson, *The C^1 generic diffeomorphism has trivial centralizer*, arXiv:0804.1416v1 (2008), https://arxiv.org/abs/0804.1416, p. 15, Proposition 2.5 (proof pp. 16)

import Mathlib
import Definitions.Def_BCWCentralizer_Basic

open scoped Manifold ContDiff Topology

namespace BCWCentralizer
theorem dense_to_residual {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (hT : Dense {f : Diff1 d M | HasTrivialLipCentralizer f}) :
    {f : Diff1 d M | HasTrivialLipCentralizer f} ∈ residual (Diff1 d M) := by sorry
end BCWCentralizer
