-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_lemma_2
-- name    : BinarySketchTruncation.Opposite.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:30.329203+00:00
-- url     : https://prove2.me/theorems/1c934408-5e6d-41a9-bf2f-542ae9b46c4f
-- title:
--   Lemma 2 — single-bit simulation
-- statement:
--   Let $p_0,p_1\in[0,1]$ be distinct. Under hypothesis $h\in\{0,1\}$ let a bit $U$ have law $\operatorname{Bernoulli}(p_h)$. Then
--
--   $$
--   U\succeq U\oplus h
--   \quad\Longleftrightarrow\quad
--   (p_0\le1/2\le p_1)\ \lor\ (p_1\le1/2\le p_0).
--   $$
--
--   The same stochastic kernel must leave the law under hypothesis zero unchanged and produce the flipped law under hypothesis one. The endpoints zero and one and either midpoint endpoint remain included, subject only to distinctness.
--
--   This is the single-coordinate comparison used in the independent-addition construction.
--
--   Differences from the source:
--   - encoding: a bit and hypotheses h=0,1 → ZMod 2 bits, Bool hypotheses and normalized Mathlib PMFs; reason: these representations preserve the two Bernoulli masses and the hypothesis-dependent flip
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 7, Lemma 2 (PDF p. 8)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

namespace BinarySketchTruncation.Opposite

/-- Lemma 2, printed p. 7 (PDF 8), including both orientations and endpoints. -/
theorem lemma_2 (p₀ p₁ : Bias) (hne : p₀ ≠ p₁) :
    Dominates (bitExperiment p₀ p₁)
      (shiftUnderOne (bitExperiment p₀ p₁) (1 : Bit)) ↔ OppositeSides p₀ p₁ := by sorry

end BinarySketchTruncation.Opposite
