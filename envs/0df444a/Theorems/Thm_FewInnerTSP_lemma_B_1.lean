-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_B_1
-- name    : FewInnerTSP.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:32:57.644795+00:00
-- url     : https://prove2.me/theorems/6c299368-4ed1-478f-ac21-7e514063f2df
-- title:
--   Lemma B.1 (Balanced squares)
-- statement:
--   Let $Q$ be a finite set of points in the plane with $|Q|>17$. A minimum-side closed axis-aligned square $\sigma^*$ containing at least $|Q|/17$ points of $Q$ exists. For every such square, with center $c$ and side $u$:
--
--   1. $u>0$;
--   2. for every $t$ with $1\le t\le3$ such that no point of $Q$ lies on the boundary of the square with center $c$ and side $tu$, that square contains at most $16|Q|/17$ points of $Q$, and at most $16|Q|/17$ points of $Q$ lie outside it.
--
--   This gives the one-parameter family of $16/17$-balanced separators $\sigma_t$, $t\in[1,3]$, over which §4 averages.
--
--   Differences from the source:
--   - generalization: Let σ∗ be a minimum-side axis-aligned square containing at least |Q|/17 points → an added clause: such a square exists; reason: the page presupposes it; stating it makes the lemma stronger
--   - encoding: at most 16|Q|/17 points on either side → 17 · #inside ≤ 16|Q| and 17 · #outside ≤ 16|Q| for the closed square; reason: integer form of the same inequality
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma B.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_FewInnerTSP_Charges

namespace FewInnerTSP

open Classical in
/-- **Lemma B.1 (Balanced squares).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A
Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma B.1, p.16 (PDF p.18):
"Let |Q| > 17. Let σ∗ be a minimum-side axis-aligned square containing at least |Q|/17 points of Q, with
side length u. Then u > 0. Every square concentric with σ∗ and of side tu, 1 ≤ t ≤ 3, has at most 16|Q|/17
points on either side when no point is on its boundary."

For a finite planar set `Q` with `|Q| > 17`: a minimum-side closed axis-aligned square containing at
least `|Q|/17` points of `Q` exists; and for every such square (center `c`, side `u`), `u > 0`, and for
every `t ∈ [1, 3]` such that no point of `Q` lies on the boundary of the concentric square of side `t u`,
both the points inside and the points outside that square number at most `16|Q|/17`.

**Formalization Note** `Q` is a `Finset`, so its points are distinct. The existence clause is the
presupposition of the page's "Let σ∗ be a minimum-side … square". -/
theorem lemma_B_1 (Q : Finset Pt) (hQ : 17 < Q.card) :
    (∃ (c : Pt) (u : ℝ), IsMinBalancingSquare Q c u) ∧
    ∀ (c : Pt) (u : ℝ), IsMinBalancingSquare Q c u →
      0 < u ∧ ∀ t : ℝ, 1 ≤ t → t ≤ 3 → (∀ x ∈ Q, x ∉ squareBoundary c (t * u)) →
        17 * (Q.filter fun x => x ∈ closedSquare c (t * u)).card ≤ 16 * Q.card ∧
        17 * (Q.filter fun x => x ∉ closedSquare c (t * u)).card ≤ 16 * Q.card := by sorry

end FewInnerTSP
