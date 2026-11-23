-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_inCH_three_tagged_union
-- name    : ApproxPolySatCH.Main.inCH_three_tagged_union
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:00.493732+00:00
-- url     : https://prove2.me/theorems/b23dae2e-0d79-4f56-9fc0-ab761fac4273
-- title:
--   CH is closed under a union of three tagged representations
-- statement:
--   Let $S,D,C$ be binary languages in the counting hierarchy. Their tagged disjoint union, using prefixes $00$, $01$ and $1$ respectively, is also in the counting hierarchy. A word outside these three tagged forms is rejected.
--
--   The tags and tag-stripping transformations are finite and fixed before the input. This packages the sparse, dense and circuit representations into one language without changing their individual acceptance semantics.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §3 encoding equivalence, p.14, and proof of Theorem 1, p.26; the three concrete tags are those of the mission's APSLanguage interface, §§2–3, pp.5–7,14–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=14

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

/-- Disjoint two-bit/one-bit representation tags may be stripped by uniform polynomial-time preprocessing. -/
theorem inCH_three_tagged_union (S D C : Language)
    (hS : InCH S) (hD : InCH D) (hC : InCH C) :
    InCH {x : Word |
      (∃ w ∈ S, x = [false, false] ++ w) ∨
      (∃ w ∈ D, x = [false, true] ++ w) ∨
      (∃ w ∈ C, x = [true] ++ w)} := by sorry
