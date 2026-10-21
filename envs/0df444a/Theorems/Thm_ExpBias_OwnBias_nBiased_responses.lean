-- Prove2me | Theorems.Thm_ExpBias_OwnBias_nBiased_responses
-- name    : ExpBias.OwnBias.nBiased_responses
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:09.486456+00:00
-- url     : https://prove2.me/theorems/bc2b2ba0-f86e-433d-90f9-ed282c2140d9
-- title:
--   Proof of Proposition 1, p. 31 — optimal responses to the signals of the n-biased experiment
-- statement:
--   Assume the standing assumptions and let $\lambda=\Lambda-1$. Consider the n-biased experiment $\sigma_n=\{\lambda,1\}$ and put
--   $$
--   t_n=\frac{v_S-v_N}{(1-\lambda)(v_W-v_S)+v_S-v_N} .
--   $$
--   Then:
--
--   1. after signal $w$, exploiting is strictly better than the status quo: $\Pr[w]\,v_S<\Pr[W\wedge w]\,v_W+\Pr[N\wedge w]\,v_N$;
--   2. after signal $n$, exploiting is strictly better than the status quo exactly when $p>t_n$:
--   $$
--   \bigl(1-P(N\mid n,\sigma_n)\bigr)v_W+P(N\mid n,\sigma_n)\,v_N>v_S\iff p>t_n ;
--   $$
--   3. $\hat p<t_n$, so for $p>\hat p$ the firm may or may not exploit after $n$.
--
--   This is the second paragraph of the proof of Proposition 1: it fixes the firm's optimal decision rule under $\sigma_n$, and its threshold $t_n$ splits the case $p>\hat p$ into the two cases of the proof.
--
--   **Formalization Note.** $P(N\mid n,\sigma_n)$ is written as $1-\Pr[W\mid n,\sigma_n]$. Item 1 is stated with joint probabilities over the event "signal $w$".
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), p. 31 (PDF 32), §7.1 proof of Proposition 1, second paragraph

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

namespace ExpBias.OwnBias

theorem nBiased_responses (P : Params) (hP : P.Standing) :
    sigProb P (nBiased P) true * P.vS <
        joint P (nBiased P) true true * P.vW + joint P (nBiased P) false true * P.vN ∧
    (P.vS < (1 - (1 - postW P (nBiased P) false)) * P.vW +
          (1 - postW P (nBiased P) false) * P.vN ↔
        (P.vS - P.vN) / ((1 - lam P) * (P.vW - P.vS) + P.vS - P.vN) < P.p) ∧
    pHat P < (P.vS - P.vN) / ((1 - lam P) * (P.vW - P.vS) + P.vS - P.vN) := by sorry

end ExpBias.OwnBias
