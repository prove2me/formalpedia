-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_lemma_3_8
-- name    : ExactLearningSeparation678.Randomized.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:40.849199+00:00
-- url     : https://prove2.me/theorems/d0027458-f47c-49fb-bb60-e3d5e1ca9e33
-- title:
--   Lemma 3.8 — removal of the active sheet
-- statement:
--   Fix any deterministic learner using at most $D$ membership queries and returning a concept in $C_t$. Let $\mu$ be the independent uniform law of the slope and polynomial coefficients, and let $A$ be the event in Eq. (12). Then
--   $$\Pr_\mu[\mathrm{success}]\le\Pr_{\mathrm{H1}}[A].$$
--   The same learner is used in both experiments, and its choices may depend on all previous answers. The event includes merely querying the sheet with address $s$, regardless of the returned bit.
--
--   This compares real identification success with the event in the concrete H1 experiment. Proper outputs use the paper's normalization; the actual complexity minima still allow arbitrary hypotheses.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
--   - encoding: the transcript contains all queries, answers, and the final output, with at most D queries → a length-D table of optional query-answer pairs, padded by none after stopping, together with the final output; reason: under MakesAtMost D the representation retains every actual observation, including repeated queries and early stopping
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Lemma 3.8 and §3.4 preamble, p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Experiments

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Lemma 3.8, p.23, with event (12), proper outputs as normalized in the section preamble. -/
theorem lemma_3_8 (m : Size) (D : ℕ) (A : Learner m) (hA : A.MakesAtMost D) :
    realSuccess m D A ≤ probability (lawH1 m D A) (eventA m D) := by sorry

end ExactLearningSeparation678.Randomized
