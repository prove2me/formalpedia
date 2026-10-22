-- Prove2me | Theorems.Thm_ExpBias_OwnBias_proposition_1
-- name    : ExpBias.OwnBias.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:17.710996+00:00
-- url     : https://prove2.me/theorems/aa2c86a0-b557-43e9-a9bd-07b43b0ad311
-- title:
--   Proposition 1, p. 13 — over E, the optimal experiment is exactly the w-biased one if p > p̂ and the n-biased one if p < p̂
-- statement:
--   Let $v_W>v_S>v_N$ be the payoffs of exploiting a working technology, keeping the status quo and exploiting a failing one, $p\in(0,1)$ the prior that the technology works, and $\Lambda\in(1,2)$ the cap on the precisions of an experiment, with $\hat p=\frac{v_S-v_N}{v_W-v_N}$ and $\lambda=\Lambda-1$. The firm chooses an experiment $\{\lambda_w,\lambda_n\}$ from $\mathbf E=\{(\lambda_w,\lambda_n)\in(0,1]^2:\ 1<\lambda_w+\lambda_n\le\Lambda\}$ and then acts optimally on its signal. Then:
--
--   1. if $p>\hat p$, an experiment is optimal in $\mathbf E$ if and only if it is the w-biased experiment $\{1,\lambda\}$;
--   2. if $p<\hat p$, an experiment is optimal in $\mathbf E$ if and only if it is the n-biased experiment $\{\lambda,1\}$.
--
--   $$
--   p>\hat p\ \Longrightarrow\ \operatorname*{arg\,max}_{e\in\mathbf E}\mathrm{value}(e)=\{(1,\lambda)\},\qquad p<\hat p\ \Longrightarrow\ \operatorname*{arg\,max}_{e\in\mathbf E}\mathrm{value}(e)=\{(\lambda,1)\}.
--   $$
--
--   A firm predisposed to exploit chooses the experiment that can only overturn its predisposition with a conclusive "no", and a firm predisposed not to exploit the one that can only overturn it with a conclusive "yes": experiment choice is biased toward the firm's own prior.
--
--   **Formalization Note.** "Optimally chooses" is read as maximising the value of the experiment over $\mathbf E$, where the value is the expected payoff under the best of the four signal-contingent decision rules; the "only if" direction formalises the paper's remark that, outside the degenerate case $p=\hat p$, these are the only experiments optimally chosen. The assumptions $0<p<1$ and $1<\Lambda$ are added to the page's (see the definitions file).
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), p. 13 (PDF 14), §2.2, Proposition 1 and the paragraph after it; proof on p. 31 (PDF 32), §7.1

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

namespace ExpBias.OwnBias

theorem proposition_1 (P : Params) (hP : P.Standing) :
    (pHat P < P.p → ∀ e : Experiment, IsOptimal P e ↔ e = wBiased P) ∧
    (P.p < pHat P → ∀ e : Experiment, IsOptimal P e ↔ e = nBiased P) := by sorry

end ExpBias.OwnBias
