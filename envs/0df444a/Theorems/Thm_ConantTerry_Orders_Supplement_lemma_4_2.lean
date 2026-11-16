-- Prove2me | Theorems.Thm_ConantTerry_Orders_Supplement_lemma_4_2
-- name    : ConantTerry.Orders.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:25:38.472197+00:00
-- url     : https://prove2.me/theorems/cbc62654-6a6c-4c3c-8bbb-426f594786de
-- title:
--   Lemma 4.2 — small covered proto-ladders yield tight ladders
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, $k\ge1$, and $\delta,\epsilon>0$. Let $I,J\subseteq[0,1]$ be intervals of length at most $\epsilon$. If $f$ admits an $(I,J)$-covered $(k,\delta+\epsilon)$-proto-ladder, meaning singleton collections $\{I\},\{J\}$ in Definition 4.1, then
--   $$
--   f\text{ admits a uniform }\epsilon\text{-tight }(k,\delta)\text{-ladder}.
--   $$
--   The conclusion has one common threshold and two small intervals controlling respectively the high region, including the diagonal, and the strictly lower region. The case $k=1$ is included. The output intervals and labels are existential; they are not required to be the input intervals and labels.
--
--   This is the conversion from the intermediate covered configuration to the tight ladder needed in Theorem 1.14.
--
--   Differences from the source:
--   - encoding: arbitrary sets X,Y and values in [0,1] → arbitrary types X,Y and the real subtype Set.Icc 0 1; reason: the subtype enforces exactly the source range and adds no finiteness, nonemptiness or regularity assumption
--   - encoding: finite binary words and 1-based finite indices → published List Bool word subtypes and zero-based Fin indices; reason: length, prefix, orientation and index inequalities are preserved by relabeling
--   - encoding: intervals in [0,1] of length at most ε → order-convex subsets of Set.Icc 0 1 with every pair at distance at most ε; reason: on the bounded real interval this is exactly the interval length condition, including every endpoint convention and degenerate intervals
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 15, Lemma 4.2; proof pp. 15–16

import Mathlib
import Definitions.Def_ConantTerry_Orders_Supplement_uniform_tight_ladders
import Definitions.Def_ConantTerry_Orders_Supplement_covered_proto_ladder

namespace ConantTerry.Orders.Supplement

/-- Lemma 4.2, pp.15-16, including k=1 and arbitrary endpoint conventions. -/
theorem lemma_4_2 {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (I J : Set (Set.Icc (0 : ℝ) 1))
    (hI : IsSmallInterval ε I) (hJ : IsSmallInterval ε J)
    (hproto : AdmitsCoveredProtoLadder f k (δ + ε) {I} {J}) :
    AdmitsTightLadder f k δ ε := by sorry

end ConantTerry.Orders.Supplement
