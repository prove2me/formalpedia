-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_lemma_3_10
-- name    : ExactLearningSeparation678.Randomized.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:51.984676+00:00
-- url     : https://prove2.me/theorems/636d86db-4080-43cd-846d-d430a72e7d93
-- title:
--   Lemma 3.10 — polynomial-to-random-function hybrid
-- statement:
--   For every $t=2^m$ with $m\ge2$, query budget $D$ and fixed deterministic learner of that budget, the joint laws of the hidden slope $s$ and full transcript $T$ in H1 and H2 satisfy
--   $$d_{\rm TV}((s,T)_{\mathrm{H1}},(s,T)_{\mathrm{H2}})\le\varepsilon_D,\qquad
--   \varepsilon_D=\binom Dt(2/t^2)^t.$$
--   Consequently, for the event $A$ of Eq. (12),
--   $$\Pr_{\mathrm{H1}}[A]\le\Pr_{\mathrm{H2}}[A]+\varepsilon_D.$$
--
--   Both the joint-law estimate and its event consequence are asserted. The slope is retained in the distributions, rather than integrated out of a transcript-only comparison.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
--   - encoding: the transcript contains all queries, answers, and the final output, with at most D queries → a length-D table of optional query-answer pairs, padded by none after stopping, together with the final output; reason: under MakesAtMost D the representation retains every actual observation, including repeated queries and early stopping
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Lemma 3.10, pp.25–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Experiments

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Lemma 3.10, pp.25–26: joint (s,T) laws and the entire event consequence, for every depth D. -/
theorem lemma_3_10 (m : Size) (D : ℕ) (A : Learner m) (hA : A.MakesAtMost D) :
    tv (lawH1 m D A) (lawH2 m D A) ≤ epsilon m D ∧
    probability (lawH1 m D A) (eventA m D) ≤
      probability (lawH2 m D A) (eventA m D) + epsilon m D := by sorry

end ExactLearningSeparation678.Randomized
