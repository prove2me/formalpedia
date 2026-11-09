-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_lemma_3_12
-- name    : ExactLearningSeparation678.Randomized.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:42.937852+00:00
-- url     : https://prove2.me/theorems/81f5a8b9-3534-4b3a-887c-9b9f24e09a64
-- title:
--   Lemma 3.12 — guessing an independent slope
-- statement:
--   In the H3 experiment for $t=2^m$, $m\ge2$, let a fixed deterministic learner make at most $D$ membership queries and output a concept in $C_t$. For the event $A$ of Eq. (12),
--   $$\Pr_{\mathrm{H3}}[A]\le\frac{D+1}{t^6}.$$
--   The event accounts for every queried sheet address and the slope of the final output. The learner's independence from the slope is a property to be proved from the computed experiment, not an assumed learner condition.
--
--   This bounds the event in the independent-block law with the exact coefficient $D+1$.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
--   - encoding: the transcript contains all queries, answers, and the final output, with at most D queries → a length-D table of optional query-answer pairs, padded by none after stopping, together with the final output; reason: under MakesAtMost D the representation retains every actual observation, including repeated queries and early stopping
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Lemma 3.12, p.27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Experiments

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Lemma 3.12, p.27: all sheet queries plus the final output give at most D+1 guesses. -/
theorem lemma_3_12 (m : Size) (D : ℕ) (A : Learner m) (hA : A.MakesAtMost D) :
    probability (lawH3 m D A) (eventA m D) ≤ (D + 1 : ℕ) / (t m : ℝ) ^ 6 := by sorry

end ExactLearningSeparation678.Randomized
