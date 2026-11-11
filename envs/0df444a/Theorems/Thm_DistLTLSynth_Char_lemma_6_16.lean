-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_6_16
-- name    : DistLTLSynth.Char.lemma_6_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:55.644006+00:00
-- url     : https://prove2.me/theorems/61392ebc-ce97-4677-bd6a-f58f12b5182a
-- title:
--   Lemma 6.16 — if π(A) is not nowhere dense, some left quotient h⁻¹A is dense
-- statement:
--   For every message adversary $A$: if $\pi(A)$ is not nowhere dense, then there is a finite graph history $h\in\Gamma^*$ with
--   $$\overline{h^{-1}A}=\Gamma^\omega .$$
--   This $h$ is the prefix used to guard the undecidable formulas (Lemma 6.17).
--
--   Differences from the source:
--   - encoding: π(A) nowhere dense in [0, 1] → IsNowhereDense (piMap '' A) in ℝ; reason: π(A) ⊆ [0, 1] and [0, 1] is closed in ℝ, so nowhere density in the subspace and in ℝ coincide
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
--   - encoding: h⁻¹A is defined for h ∈ Pref(A) → leftQuot h A for every h (empty when h ∉ Pref(A)); reason: a dense subset of the nonempty space Γ^ω is nonempty, so the h found lies in Pref(A)
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 28 (PDF 29), Lemma 6.16

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric

namespace DistLTLSynth.Char

/-- Lemma 6.16: if `π(A)` is not nowhere dense, some left quotient `h⁻¹A` is dense in `Γ^ω`. -/
theorem lemma_6_16 (A : Set (ℕ → CommGraph)) (hA : ¬ IsNowhereDense (piMap '' A)) :
    ∃ h : List CommGraph, Dense (leftQuot h A) := by sorry

end DistLTLSynth.Char
