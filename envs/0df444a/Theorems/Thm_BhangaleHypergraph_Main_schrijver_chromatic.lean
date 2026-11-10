-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_schrijver_chromatic
-- name    : BhangaleHypergraph.Main.schrijver_chromatic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:05:59.399728+00:00
-- url     : https://prove2.me/theorems/d693de5d-98ed-48d8-99fa-8455d35ac7e5
-- title:
--   Theorem 2.8 — Schrijver chromatic number
-- statement:
--   For natural integers $1\le h$ and $2h\le m$, let $SG(m,h)$ be the graph on stable $h$-subsets of the cyclic order on $[m]$, with disjointness as adjacency. Then
--   $$\chi(SG(m,h))=m-2h+2.$$
--   The statement includes both the upper and lower bounds, including defect zero.
--
--   This equality provides the full source chromatic-number theorem.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: the ordinary finite chromatic number → Mathlib chromaticNumber, with the finite right-hand side embedded in its extended natural codomain; reason: these graphs are finite and the equality asserts the same integer value
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Theorem 2.8, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

namespace BhangaleHypergraph.Main

theorem schrijver_chromatic (m h : ℕ) (hh : 1 ≤ h) (hm : 2 * h ≤ m) :
    (Schrijver m h).chromaticNumber = ↑(m - 2 * h + 2) := by sorry

end BhangaleHypergraph.Main
