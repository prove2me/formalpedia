-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_schrijver_colorable_upper
-- name    : BhangaleHypergraph.Main.schrijver_colorable_upper
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T08:26:46.881677+00:00
-- url     : https://prove2.me/theorems/f5bda83e-1222-44e8-8a36-be51ed2c963d
-- title:
--   Theorem 2.8, upper bound — elementary Schrijver coloring
-- statement:
--   For $1\le h$ and $2h\le m$, the Schrijver graph $SG(m,h)$ admits a proper coloring with $m-2h+2$ colors:
--   $$
--   SG(m,h)\text{ is }(m-2h+2)\text{-colorable}.
--   $$
--   This is the elementary upper-bound half of Theorem 2.8. The same coloring also works for the full Kneser graph on all $h$-subsets; cyclic stability is needed only for the complementary lower bound.
-- source:
--   Amey Bhangale, STOC 2027 submission #1052, Theorem 2.8, p. 9 (upper-bound half); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

theorem BhangaleHypergraph.Main.schrijver_colorable_upper (m h : ℕ) (hh : 1 ≤ h) (hm : 2 * h ≤ m) :
    (BhangaleHypergraph.Main.Schrijver m h).Colorable (m - 2 * h + 2) := by sorry
