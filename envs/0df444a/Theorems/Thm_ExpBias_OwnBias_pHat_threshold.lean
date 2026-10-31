-- Prove2me | Theorems.Thm_ExpBias_OwnBias_pHat_threshold
-- name    : ExpBias.OwnBias.pHat_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:10.190508+00:00
-- url     : https://prove2.me/theorems/1ea68704-d589-4001-b000-26767212af69
-- title:
--   §2, p. 11 — absent information the firm exploits iff p ≥ p̂ = (v_S − v_N)/(v_W − v_N)
-- statement:
--   Under the standing assumptions ($v_W>v_S>v_N$, $0<p<1$, $1<\Lambda<2$), the no-information threshold $\hat p=\frac{v_S-v_N}{v_W-v_N}$ lies strictly between $0$ and $1$, and exploiting without any experiment is at least as good as the status quo exactly when the prior is at least $\hat p$:
--   $$
--   0<\hat p<1,\qquad p\,v_W+(1-p)\,v_N\ \ge\ v_S\iff p\ge\hat p .
--   $$
--   The threshold $\hat p$ separates the firms predisposed to exploit from those predisposed not to; Proposition 1 shows it also decides which biased experiment the firm prefers.
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), p. 11 (PDF 12), §2

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

namespace ExpBias.OwnBias

theorem pHat_threshold (P : Params) (hP : P.Standing) :
    0 < pHat P ∧ pHat P < 1 ∧
      (P.vS ≤ P.p * P.vW + (1 - P.p) * P.vN ↔ pHat P ≤ P.p) := by sorry

end ExpBias.OwnBias
