-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_2_3
-- name    : DistLTLSynth.Char.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:36.943301+00:00
-- url     : https://prove2.me/theorems/527634e2-60a9-4cb8-8ef0-24b370af85f5
-- title:
--   Lemma 2.3 — h is a prefix of k iff J(k) ⊆ J(h)
-- statement:
--   For finite graph histories $h,k\in\Gamma^*$,
--   $$h \text{ is a prefix of } k \iff J(k)\subseteq J(h),$$
--   where $J(h)=[\,j(h)/3^{|h|},(j(h)+1)/3^{|h|}\,]$. It says that the intervals $J$ form a ternary subdivision tree matching the prefix order, the basis of every geometric argument about $\pi$.
--
--   Differences from the source:
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 7 (PDF 8), Lemma 2.3

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric

namespace DistLTLSynth.Char

/-- Lemma 2.3: for finite graph histories `h, k`, `h` is a prefix of `k` iff `J(k) ⊆ J(h)`. -/
theorem lemma_2_3 (h k : List CommGraph) : h <+: k ↔ J k ⊆ J h := by sorry

end DistLTLSynth.Char
