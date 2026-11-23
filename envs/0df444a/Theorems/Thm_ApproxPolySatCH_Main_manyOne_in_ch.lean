-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_manyOne_in_ch
-- name    : ApproxPolySatCH.Main.manyOne_in_ch
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:59.611956+00:00
-- url     : https://prove2.me/theorems/9c527ca2-3d24-4b78-a4c0-e934ebf90db5
-- title:
--   Polynomial-time many-one downward closure of CH
-- statement:
--   Suppose $L\le_m^P A$ by a total polynomial-time computable word transformation, so that for every binary word $x$,
--   $$x\in L\quad\Longleftrightarrow\quad f(x)\in A.$$
--   If $A$ belongs to the counting hierarchy, then so does $L$.
--
--   The same deterministic preprocessing machine and polynomial clock work on every word, including malformed encodings. This interface transfers CH membership between equivalent polynomial input representations.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §3 encoding robustness and Proposition 6, p.14, used in the proof of Theorem 1, p.26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=14

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

/-- Membership in CH is preserved backwards along polynomial-time many-one reductions. -/
theorem manyOne_in_ch {L A : Language} (hred : ManyOneReduction L A)
    (hA : InCH A) : InCH L := by sorry
