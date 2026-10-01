-- Prove2me | Theorems.Thm_BCWCentralizer_main_theorem
-- name    : BCWCentralizer.main_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:41:01.589732+00:00
-- url     : https://prove2.me/theorems/c51a9dbb-00d9-41eb-a1b4-f59a623595c7
-- title:
--   Main Theorem: the $C^1$-generic diffeomorphism has trivial centralizer
-- statement:
--   Let $M$ be a closed (compact, without boundary), connected smooth manifold of dimension $d$. There is a residual subset $\mathcal R\subset\mathrm{Diff}^1(M)$ (for the $C^1$ topology) such that for every $f\in\mathcal R$ and every $g\in\mathrm{Diff}^1(M)$,
--   $$fg=gf\ \Longrightarrow\ g=f^n\ \text{ for some } n\in\mathbb Z.$$
--   Equivalently, the set of $C^1$ diffeomorphisms with trivial centralizer $Z^1(f)=\langle f\rangle$ is residual.
--
--   This answers the second (and hence the first) part of Smale's question on the genericity of trivial centralizers in the $C^1$ topology.
--
--   **Formalization Note** "Residual" is Mathlib's residual filter (containing a countable intersection of dense open sets). The $C^1$ topology is the topology induced by $f\mapsto Tf$ into the compact-open topology on continuous self-maps of $TM$.
-- source:
--   Bonatti, Crovisier, Wilkinson, *The C^1 generic diffeomorphism has trivial centralizer*, arXiv:0804.1416v1 (2008), https://arxiv.org/abs/0804.1416, p. 3, Main Theorem

import Mathlib
import Definitions.Def_BCWCentralizer_Basic

open scoped Manifold ContDiff Topology

namespace BCWCentralizer
theorem main_theorem {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] :
    {f : Diff1 d M | HasTrivialCentralizer f} ∈ residual (Diff1 d M) := by sorry
end BCWCentralizer
