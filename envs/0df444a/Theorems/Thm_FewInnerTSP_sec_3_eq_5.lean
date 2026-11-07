-- Prove2me | Theorems.Thm_FewInnerTSP_sec_3_eq_5
-- name    : FewInnerTSP.sec_3_eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:48.837951+00:00
-- url     : https://prove2.me/theorems/76cbca6e-40e5-45b7-821b-93db12f64ee2
-- title:
--   §3, (5) — an optimal tour has no crossing and visits the hull in order, with interior chains in the gaps
-- statement:
--   Let $P$ be $n\ge3$ points in general position, $h_0,\dots,h_{h-1}$ a counterclockwise order of the hull vertices, $I$ the interior points and $k=|I|$. Let $\pi$ be a shortest tour. Then:
--
--   1. **No crossing.** No two edges of $\pi$ with four distinct endpoints meet; in general position every meeting of such segments would be a proper crossing.
--   2. **Chain form.** There are ordered chains $S_0,\dots,S_{h-1}$ of interior points, disjoint and together partitioning $I$ (empty chains allowed), such that after choosing an orientation $\pi$ is the cycle
--   $$h_0,S_0,h_1,S_1,\dots,h_{h-1},S_{h-1},h_0,$$
--   and at most $k$ of the chains are nonempty.
--   3. **The case $k=0$.** If $k=0$, the hull cycle $h_0,\dots,h_{h-1}$ is a shortest tour.
--
--   This is the structure every later step of the algorithm relies on: hull vertices occur in boundary order, and interior points only form chains inserted into gaps.
--
--   **Formalization Note** "After choosing one orientation" is the freedom of rotating and reversing the tour's sequence; the start $h_0$ is any hull vertex.
--
--   Differences from the source:
--   - reading: the sentences justifying (5): the 2-opt exchange strictly decreases length, and a simple closed polygon visits its hull vertices in boundary order → not stated as separate clauses; the conclusions they justify (no crossing, chain form) are clauses 1 and 2; reason: they are the page's reasons for (5), cited from [DHOW06], not further conclusions
--   - encoding: no proper crossing → the segments of two tour edges with four distinct endpoint indices are disjoint; reason: in general position a meeting of such segments is a proper crossing
--   - encoding: after choosing one orientation an optimal tour has the form (5) → the concatenation h₀ :: S₀ ++ … is a rotation of π's sequence or of its reversal; reason: a tour is its cyclic sequence up to rotation and reversal
--   - encoding: a set of points in the plane → an indexed list P : Fin n → EuclideanSpace ℝ (Fin 2), with general position over distinct indices and no separate distinctness hypothesis; reason: no three collinear forces distinct points for n ≥ 3; the Euclidean, not the sup, metric
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §3, display (5), p.3 (PDF p.5)

import Mathlib
import Definitions.Def_FewInnerTSP_HullOrder

namespace FewInnerTSP

/-- **§3, (5): hull order and the tour form.** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior
Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), §3, display (5),
p.3 (PDF p.5): "In general position an optimal tour has no proper crossing … A simple closed polygon
visits its convex-hull vertices in their boundary order, up to reversal. … Consequently, after choosing
one orientation an optimal tour has the form h0, S0, h1, S1, …, hh−1, Sh−1, h0, (5) where the Sj are
disjoint ordered chains partitioning I, and empty chains are allowed. At most k chains are nonempty. The
case k = 0 is solved directly by the hull cycle."

For `n ≥ 3` points in general position, a counterclockwise hull order `hull`, and a shortest tour `π`:
1. no two tour edges with four distinct endpoints meet (in general position every meeting of such
   segments is a proper crossing);
2. there are chains `S j` such that `π`, up to rotation and reversal, is `h₀, S₀, h₁, S₁, …`, the chains
   partitioning the interior indices, and at most `k` of them are nonempty;
3. if `k = 0`, the hull cycle `h₀, …, h_{h−1}` is a shortest tour.

**Formalization Note** The page states (5) as unnumbered text with a display; it is cited as `§3, (5)`.
The hull start `h₀` is arbitrary. -/
theorem sec_3_eq_5 (n : ℕ) (hn : 3 ≤ n) (P : Fin n → Pt) (hP : GeneralPos P) (h : ℕ)
    (hull : Fin h → Fin n) (hH : IsHullOrder P hull) (π : Equiv.Perm (Fin n))
    (hπ : IsShortestTour P π) :
    (∀ i j : Fin n,
      π i ≠ π j → π i ≠ π (finRotate n j) → π (finRotate n i) ≠ π j →
        π (finRotate n i) ≠ π (finRotate n j) →
        (segment ℝ (P (π i)) (P (π (finRotate n i))) ∩
          segment ℝ (P (π j)) (P (π (finRotate n j)))) = ∅) ∧
    (∃ S : Fin h → List (Fin n), HasChainForm P hull S π ∧
      (Finset.univ.filter fun j => S j ≠ []).card ≤ interiorCount P) ∧
    (interiorCount P = 0 → ∃ τ : Equiv.Perm (Fin n), List.ofFn τ = List.ofFn hull ∧
      IsShortestTour P τ) := by sorry

end FewInnerTSP
