-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_proposition_31
-- name    : APrioriTSP.Sampling.proposition_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:30.203743+00:00
-- url     : https://prove2.me/theorems/f7730e0b-7b8a-49d6-806c-94b67418eace
-- title:
--   Proposition 31, p. 30 — for 0 < x < y < 1, x/y − x < ln(1 − x)/ln(1 − y) < x/y
-- statement:
--   Let $0 < x < y < 1$. Then
--   $$\frac xy - x \;<\; \frac{\ln(1-x)}{\ln(1-y)} \;<\; \frac xy .$$
--
--   This elementary estimate is used in the proof of Lemma 32 (with $x = p/2$, $y = p$) to choose the number of copies of a customer in the reduction to normalized instances.
--
--   Differences from the source: none.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 30, Proposition 31

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace APrioriTSP.Sampling

/-- Proposition 31 (p. 30): for `0 < x < y < 1`,
`x/y − x < ln(1 − x)/ln(1 − y) < x/y`. -/
theorem proposition_31 (x y : ℝ) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    x / y - x < Real.log (1 - x) / Real.log (1 - y) ∧
      Real.log (1 - x) / Real.log (1 - y) < x / y := by sorry

end APrioriTSP.Sampling
