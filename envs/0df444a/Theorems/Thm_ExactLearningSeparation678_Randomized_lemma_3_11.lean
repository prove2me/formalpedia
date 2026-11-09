-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_lemma_3_11
-- name    : ExactLearningSeparation678.Randomized.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:01.079497+00:00
-- url     : https://prove2.me/theorems/bc717f95-cc85-44b3-994c-b8dcc700385b
-- title:
--   Lemma 3.11 — independent-block hybrid
-- statement:
--   For every $t=2^m$ with $m\ge2$ and every fixed deterministic learner making at most $D$ queries, the joint laws of $(s,T)$ in H2 and H3 satisfy
--   $$d_{\rm TV}((s,T)_{\mathrm{H2}},(s,T)_{\mathrm{H3}})\le\binom D2/t^6.$$
--   Consequently, for the event $A$ of Eq. (12),
--   $$\Pr_{\mathrm{H2}}[A]\le\Pr_{\mathrm{H3}}[A]+\binom D2/t^6.$$
--   H3 assigns each block one independent uniform address, sampled once and retained throughout all repeated queries.
--
--   This is the complete joint-law and event comparison with the independent-block experiment.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
--   - encoding: the transcript contains all queries, answers, and the final output, with at most D queries → a length-D table of optional query-answer pairs, padded by none after stopping, together with the final output; reason: under MakesAtMost D the representation retains every actual observation, including repeated queries and early stopping
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Lemma 3.11, pp.26–27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Experiments

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Lemma 3.11, pp.26–27: independent labels are sampled once, and the slope is retained in both laws. -/
theorem lemma_3_11 (m : Size) (D : ℕ) (A : Learner m) (hA : A.MakesAtMost D) :
    tv (lawH2 m D A) (lawH3 m D A) ≤ collisionError m D ∧
    probability (lawH2 m D A) (eventA m D) ≤
      probability (lawH3 m D A) (eventA m D) + collisionError m D := by sorry

end ExactLearningSeparation678.Randomized
