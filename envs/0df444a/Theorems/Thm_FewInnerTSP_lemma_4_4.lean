-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_4_4
-- name    : FewInnerTSP.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:14.692877+00:00
-- url     : https://prove2.me/theorems/aab28fec-a5a6-48a6-9f0c-5f979fce1f4d
-- title:
--   Lemma 4.4 (Boundary contribution)
-- statement:
--   In normalized coordinates, let $W$ be any finite planar set (the skeleton's vertices) and $H$ any finite set of $h$ points on the boundary of the convex hull of $W$, placed arbitrarily. The boundary charge
--   $$E_H(t)=\sum_{s,\ g\ \text{active}}\log_2(1+h_g),\qquad h_g=|H\cap D_g|,$$
--   satisfies $\mathbb E_tE_H(t)=O(\log^2(h+2))$ for $t$ uniform on $[1,3]$: there is an absolute constant $C>0$ with
--   $$\mathbb E_t\,E_H(t)\le C\log_2^2(h+2).$$
--
--   Together with Lemma 4.2 this splits the logarithm of the number of crossing choices into $O(\sqrt a)$ for the core and a polylogarithm for the skeleton, which is what replaces $k^{O(\sqrt k)}$ by $2^{O(\sqrt k)}$.
--
--   Differences from the source:
--   - generalization: vertex locations on the fixed convex boundary → any finite H on the frontier of the convex hull of any finite W, with C fixed before W and H; reason: the skeleton is one such W, and recursive calls keep subsets of its vertices
--   - encoding: E_t E_H(t) = O(log²(h + 2)) → (1/2)∫⁻ over [1,3] of the ℝ≥0∞-valued charge ≤ C (log₂(h+2))²; reason: O-notation with the constant before the input; the base of the logarithm is absorbed in C
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_FewInnerTSP_Charges

namespace FewInnerTSP

open scoped ENNReal

/-- **Lemma 4.4 (Boundary contribution).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A
Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.4, p.7 (PDF p.9): "For
arbitrary vertex locations on the fixed convex boundary, EtEH(t) = O(log²(h + 2))."

There is a constant `C > 0` such that for every finite planar set `W` (the skeleton's vertices) and every
finite set `H` of `h` points on the boundary of the convex hull of `W`, the expectation over `t` uniform
on `[1, 3]` of the boundary charge `E_H(t) = Σ_{s, g active} log₂(1 + h_g)` is at most
`C log₂²(h + 2)`.

**Formalization Note** `H` is any subset of the convex boundary (recursive calls lose skeleton vertices);
the convex curve is the boundary of the skeleton's hull, not of the recursive vertex set. -/
theorem lemma_4_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ W H : Finset Pt, (H : Set Pt) ⊆ frontier (convexHull ℝ (W : Set Pt)) →
      expectedCharge H ≤ ENNReal.ofReal (C * Real.logb 2 ((H.card : ℝ) + 2) ^ 2) := by sorry

end FewInnerTSP
