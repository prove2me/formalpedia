-- Prove2me | Theorems.Thm_BCWCentralizer_usc_continuity_points_residual
-- name    : BCWCentralizer.usc_continuity_points_residual
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:13:25.570537+00:00
-- url     : https://prove2.me/theorems/2b751f7a-5ed7-43f2-86e6-f7fd8968b1bc
-- title:
--   Continuity points of an upper-semicontinuous compact-valued map are residual
-- statement:
--   Let $B$ be a Baire space, let $X$ be a compact metric space, and let $\mathcal K(X)$ be the space of non-empty compact subsets of $X$ with the Hausdorff distance $d_H$. Let $h:B\to\mathcal K(X)$ be upper-semicontinuous: for every $b\in B$ and every open $U\supseteq h(b)$ we have $h(b')\subseteq U$ for all $b'$ in a neighbourhood of $b$. Then
--   $$\{b\in B:\ h \text{ is continuous at } b \text{ for } d_H\}$$
--   is a residual subset of $B$.
--
--   This classical fact is the engine of the passage from "dense" to "residual" in Proposition 2.5, applied to $f\mapsto Z^{\mathrm{Lip}}(f)\cap\mathrm{Lip}_K(M)$.
--
--   **Formalization Note** The paper phrases upper-semicontinuity with sequences ($b_n\to b\Rightarrow\limsup h(b_n)\subseteq h(b)$); the neighbourhood formulation used here is the standard one for compact-valued maps and implies the sequential one.
-- source:
--   Bonatti, Crovisier, Wilkinson, *The C^1 generic diffeomorphism has trivial centralizer*, arXiv:0804.1416v1 (2008), https://arxiv.org/abs/0804.1416, p. 16, the classical Proposition quoted in the proof of Proposition 2.5

import Mathlib

open scoped Topology

namespace BCWCentralizer
theorem usc_continuity_points_residual {B X : Type*} [TopologicalSpace B] [BaireSpace B]
    [MetricSpace X] [CompactSpace X] (h : B → TopologicalSpace.NonemptyCompacts X)
    (husc : ∀ b : B, ∀ U : Set X, IsOpen U → (h b : Set X) ⊆ U →
      ∀ᶠ b' in 𝓝 b, (h b' : Set X) ⊆ U) :
    {b : B | ContinuousAt h b} ∈ residual B := by sorry
end BCWCentralizer
