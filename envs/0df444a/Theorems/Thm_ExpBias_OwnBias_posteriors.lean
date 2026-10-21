-- Prove2me | Theorems.Thm_ExpBias_OwnBias_posteriors
-- name    : ExpBias.OwnBias.posteriors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:19.168394+00:00
-- url     : https://prove2.me/theorems/3fcda353-c353-4408-a600-5772251b8f11
-- title:
--   §2.1, p. 12, and p. 31 — posteriors of the w-biased and n-biased experiments
-- statement:
--   Assume the standing assumptions. Under the w-biased experiment $\sigma_w=\{1,\lambda\}$ and the n-biased experiment $\sigma_n=\{\lambda,1\}$, where $\lambda=\Lambda-1$, both signals of each experiment have positive probability, and:
--
--   1. after signal $n$ under $\sigma_w$ the state is surely $N$: $\Pr[W\mid n,\sigma_w]=0$;
--   2. after signal $w$ under $\sigma_n$ the state is surely $W$: $\Pr[W\mid w,\sigma_n]=1$;
--   3. the remaining posteriors are
--   $$
--   P(W\mid w,\sigma_w)=\frac{p}{p+(1-\lambda)(1-p)},\qquad P(N\mid n,\sigma_n)=\frac{1-p}{p(1-\lambda)+1-p}.
--   $$
--
--   These are the posteriors on which the firm's optimal responses in the proof of Proposition 1 are computed.
--
--   **Formalization Note.** $P(N\mid n,\sigma_n)$ is written as $1-\Pr[W\mid n,\sigma_n]$. The positivity of the four signal probabilities is stated so that the posteriors are genuine conditional probabilities and not the value of a division by zero.
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), p. 12 (PDF 13), §2.1; p. 31 (PDF 32), proof of Proposition 1

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

namespace ExpBias.OwnBias

theorem posteriors (P : Params) (hP : P.Standing) :
    (0 < sigProb P (wBiased P) true ∧ 0 < sigProb P (wBiased P) false ∧
      0 < sigProb P (nBiased P) true ∧ 0 < sigProb P (nBiased P) false) ∧
    postW P (wBiased P) false = 0 ∧
    postW P (nBiased P) true = 1 ∧
    postW P (wBiased P) true = P.p / (P.p + (1 - lam P) * (1 - P.p)) ∧
    1 - postW P (nBiased P) false = (1 - P.p) / (P.p * (1 - lam P) + 1 - P.p) := by sorry

end ExpBias.OwnBias
