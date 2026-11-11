-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_2_4
-- name    : DistLTLSynth.Char.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:46.72345+00:00
-- url     : https://prove2.me/theorems/45f482ae-5e10-4992-9514-51523a772f49
-- title:
--   Lemma 2.4 — π : Γ^ω → [0, 1] is continuous and surjective
-- statement:
--   The map $\pi:\Gamma^\omega\to[0,1]$, with $\Gamma^\omega$ carrying the product topology of the discrete $\Gamma$, is continuous and surjective:
--   $$\pi \text{ continuous}\quad\text{and}\quad \pi(\Gamma^\omega)=[0,1].$$
--   This is what makes $\pi(A)$ a faithful picture of $A$ (e.g. $\pi(\Gamma^\omega)=[0,1]$, and closures commute with $\pi$).
--
--   Differences from the source:
--   - encoding: π : Γ^ω → [0, 1] → piMap : (ℕ → CommGraph) → ℝ with Set.range piMap = Set.Icc 0 1; reason: the range equation states both the codomain and surjectivity
--   - encoding: j(h) is the left-to-right index of h's edge in the inputless round-|h| view complex; π(h) is the common point of the nested intervals J(h[...r]) → j is defined by the recursion of Lemma 4.4 (jIdx), and piMap w is the supremum of the left endpoints j(w[...r])/3^r; reason: Lemma 4.4 proves the recursion for the geometric index; the left endpoints of nested intervals of length 3^{-r} increase to their common point
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 7 (PDF 8), Lemma 2.4

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric

namespace DistLTLSynth.Char

/-- Lemma 2.4: `π : Γ^ω → [0, 1]` is continuous and surjective (`Γ^ω` with the product
topology of discrete `Γ`). -/
theorem lemma_2_4 : Continuous piMap ∧ Set.range piMap = Set.Icc (0 : ℝ) 1 := by sorry

end DistLTLSynth.Char
