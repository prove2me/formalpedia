-- Prove2me | Theorems.Thm_ExpBias_OwnBias_wBiased_responses
-- name    : ExpBias.OwnBias.wBiased_responses
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:14.518982+00:00
-- url     : https://prove2.me/theorems/376b5329-9dd4-496e-85d5-5a1ae4fcd3db
-- title:
--   Proof of Proposition 1, p. 31 — optimal responses to the signals of the w-biased experiment
-- statement:
--   Assume the standing assumptions and let $\lambda=\Lambda-1$. Consider the w-biased experiment $\sigma_w=\{1,\lambda\}$ and put
--   $$
--   t_w=\frac{(1-\lambda)(v_S-v_N)}{v_W-v_S+(1-\lambda)(v_S-v_N)} .
--   $$
--   Then:
--
--   1. after signal $n$, not exploiting is strictly better than exploiting: $\Pr[W\wedge n]\,v_W+\Pr[N\wedge n]\,v_N<\Pr[n]\,v_S$;
--   2. after signal $w$, exploiting is strictly better than the status quo exactly when $p>t_w$:
--   $$
--   P(W\mid w,\sigma_w)\,v_W+\bigl(1-P(W\mid w,\sigma_w)\bigr)v_N>v_S\iff p>t_w ;
--   $$
--   3. $t_w<\hat p$, so after $w$ the firm exploits whenever $p>\hat p$.
--
--   This is the first paragraph of the proof of Proposition 1: it fixes the firm's optimal decision rule under $\sigma_w$.
--
--   **Formalization Note.** Item 1 is stated with joint probabilities (expected payoffs over the event "signal $n$") rather than with the posterior, which is $0$ here.
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), p. 31 (PDF 32), §7.1 proof of Proposition 1, first paragraph

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

namespace ExpBias.OwnBias

theorem wBiased_responses (P : Params) (hP : P.Standing) :
    joint P (wBiased P) true false * P.vW + joint P (wBiased P) false false * P.vN <
        sigProb P (wBiased P) false * P.vS ∧
    (P.vS < postW P (wBiased P) true * P.vW + (1 - postW P (wBiased P) true) * P.vN ↔
        (1 - lam P) * (P.vS - P.vN) / (P.vW - P.vS + (1 - lam P) * (P.vS - P.vN)) < P.p) ∧
    (1 - lam P) * (P.vS - P.vN) / (P.vW - P.vS + (1 - lam P) * (P.vS - P.vN)) < pHat P := by sorry

end ExpBias.OwnBias
