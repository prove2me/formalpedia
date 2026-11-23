-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_schrijver_chromatic_lower
-- name    : BhangaleHypergraph.Main.schrijver_chromatic_lower
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T08:27:41.75795+00:00
-- url     : https://prove2.me/theorems/7b674200-2d50-4e55-84de-a8c0706b21df
-- title:
--   Theorem 2.8, lower bound — Schrijver chromatic number
-- statement:
--   For $1\le h$ and $2h\le m$, every proper coloring of the Schrijver graph $SG(m,h)$ requires at least $m-2h+2$ colors:
--   $$
--   m-2h+2\le \chi(SG(m,h)).
--   $$
--   This is the topological lower-bound half of Schrijver's theorem. Unlike the elementary upper coloring, it essentially uses cyclic stability of the vertices. In the formal statement the finite lower bound is embedded in $\mathbb N\cup\{\infty\}$, the codomain of `SimpleGraph.chromaticNumber`.
-- source:
--   Amey Bhangale, STOC 2027 submission #1052, Theorem 2.8, p. 9 (lower-bound half), citing A. Schrijver [Sch78]; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

theorem BhangaleHypergraph.Main.schrijver_chromatic_lower (m h : ℕ) (hh : 1 ≤ h) (hm : 2 * h ≤ m) :
    ((m - 2 * h + 2 : ℕ) : ℕ∞) ≤ (BhangaleHypergraph.Main.Schrijver m h).chromaticNumber := by sorry
