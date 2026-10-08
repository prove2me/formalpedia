-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_lemma_3
-- name    : AdaptiveStepIPM.PredCorr.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:04.204647+00:00
-- url     : https://prove2.me/theorems/93ccfb69-8455-46ae-93a5-753cd1068b0f
-- title:
--   Lemma 3 — the corrector returns to N₂(1/4)
-- statement:
--   An iteration of Algorithm 1 that starts in $N_2(1/4)$ returns to $N_2(1/4)$:
--
--   $$(x,s)\in N_2(1/4),\quad (x,s)\longmapsto(x^+,s^+)\quad\Longrightarrow\quad(x^+,s^+)\in N_2(1/4).$$
--
--   This one-iteration invariant yields the paper's assertion that every iterate of a run lies in the inner neighborhood.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 7, Lemma 3

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 3, printed p. 7, in its equivalent one-iteration invariant form. -/
theorem lemma_3 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hstep : Alg1Step A b c x s xNext sNext) :
    N2 A b c (1 / 4) xNext sNext := by sorry

end AdaptiveStepIPM.PredCorr
