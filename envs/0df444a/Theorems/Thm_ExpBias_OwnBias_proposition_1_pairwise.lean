-- Prove2me | Theorems.Thm_ExpBias_OwnBias_proposition_1_pairwise
-- name    : ExpBias.OwnBias.proposition_1_pairwise
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:15.243981+00:00
-- url     : https://prove2.me/theorems/edb5f5c5-a127-4d5e-acc4-23a22eac4312
-- title:
--   Proposition 1, pairwise form, p. 13 — the w-biased experiment beats the n-biased one iff p > p̂
-- statement:
--   Assume the standing assumptions. Comparing only the two biased experiments $\sigma_w=\{1,\lambda\}$ and $\sigma_n=\{\lambda,1\}$, each valued at the firm's best signal-contingent decision rule,
--   $$
--   p>\hat p\implies \mathrm{value}(\sigma_n)<\mathrm{value}(\sigma_w),\qquad p<\hat p\implies \mathrm{value}(\sigma_w)<\mathrm{value}(\sigma_n).
--   $$
--   This is the choice "between the w-biased and n-biased experiment" that Proposition 1 describes: a firm that would exploit without experimenting prefers the experiment whose only decisive signal is bad news. The goal of the mission strengthens it to optimality over the whole experiment set.
--
--   **Formalization Note.** The inequalities are strict; strictness uses $0<p<1$ and $\lambda>0$ (that is, $\Lambda>1$).
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), p. 13 (PDF 14), §2.2, Proposition 1 and the paragraph after it; proof on p. 31 (PDF 32)

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

namespace ExpBias.OwnBias

theorem proposition_1_pairwise (P : Params) (hP : P.Standing) :
    (pHat P < P.p → value P (nBiased P) < value P (wBiased P)) ∧
    (P.p < pHat P → value P (wBiased P) < value P (nBiased P)) := by sorry

end ExpBias.OwnBias
