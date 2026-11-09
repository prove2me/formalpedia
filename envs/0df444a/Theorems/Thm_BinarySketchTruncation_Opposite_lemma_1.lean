-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_lemma_1
-- name    : BinarySketchTruncation.Opposite.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:35.016224+00:00
-- url     : https://prove2.me/theorems/d77b59c9-057c-4e29-b36d-5ea909d69dbf
-- title:
--   Lemma 1 — reduction to deterministic vectors
-- statement:
--   Let $U$ have any conditional laws $P_0,P_1$ on $\mathbb F_2^k$. For every deterministic $v\in\mathbb F_2^k$, let $V_v$ be zero under hypothesis zero and equal to $v$ under hypothesis one. If $U\succeq U\oplus V_v$ for every $v$, then
--
--   $$
--   \forall(\nu_0,\nu_1),\qquad U\succeq U\oplus V,
--   $$
--
--   where $V$ has law $\nu_h$ and is independent of $U$ conditional on each hypothesis $h$. The laws $\nu_0$ and $\nu_1$ are arbitrary and may differ.
--
--   The result supplies a comparison for every independent addition from comparisons for the source's deterministic shifts. It includes dimension zero and does not specialize $U$ to a Bernoulli product law.
--
--   Differences from the source:
--   - encoding: finite binary vectors and hypothesis-indexed probability laws → Fin-indexed ZMod 2 vectors, Bool hypotheses, and normalized Mathlib PMFs; reason: these are the same finite objects and conditional laws; false denotes 0, true denotes 1, and addition is XOR
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 7, Lemma 1 (PDF p. 8)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

namespace BinarySketchTruncation.Opposite

/-- Lemma 1, printed p. 7 (PDF 8): both independent laws are arbitrary. -/
theorem lemma_1 (k : ℕ) (U : Experiment (Vec k))
    (hdet : ∀ v : Vec k, Dominates U (shiftUnderOne U v)) :
    ∀ ν : Experiment (Vec k), Dominates U (independentSum U ν) := by sorry

end BinarySketchTruncation.Opposite
