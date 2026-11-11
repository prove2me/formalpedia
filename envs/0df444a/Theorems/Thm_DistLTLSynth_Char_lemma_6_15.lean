-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_6_15
-- name    : DistLTLSynth.Char.lemma_6_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:53.107641+00:00
-- url     : https://prove2.me/theorems/fc488f66-c779-4843-a2ce-ab5b53a5d476
-- title:
--   Lemma 6.15 — π(A) nowhere dense iff every finite history has a non-live extension
-- statement:
--   For every message adversary $A\subseteq\Gamma^\omega$,
--   $$\pi(A)\text{ is nowhere dense in }[0,1]\iff \forall h\in\Gamma^*\ \exists k\in\Gamma^*:\ h\cdot k\notin\mathrm{Pref}(A),$$
--   i.e. every finite graph history has an extension that is not live under $A$. It translates the geometric condition into a combinatorial one on prefixes.
--
--   Differences from the source:
--   - encoding: π(A) nowhere dense in [0, 1] → IsNowhereDense (piMap '' A) in ℝ; reason: π(A) ⊆ [0, 1] and [0, 1] is closed in ℝ, so nowhere density in the subspace and in ℝ coincide
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 28 (PDF 29), Lemma 6.15

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric

namespace DistLTLSynth.Char

/-- Lemma 6.15: `π(A)` is nowhere dense iff every finite graph history `h` has an extension
`h · k` that is not live under `A` (not in `Pref(A)`). -/
theorem lemma_6_15 (A : Set (ℕ → CommGraph)) :
    IsNowhereDense (piMap '' A) ↔
      ∀ h : List CommGraph, ∃ k : List CommGraph, h ++ k ∉ Pref A := by sorry

end DistLTLSynth.Char
