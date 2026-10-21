-- Prove2me | Theorems.Thm_ExpBias_OwnBias_frontier_display_kink
-- name    : ExpBias.OwnBias.frontier_display_kink
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:15.267699+00:00
-- url     : https://prove2.me/theorems/998bca67-b741-4c56-82cc-6c999d053864
-- title:
--   §2.2, pp. 13–14 — the display V of the rule exploit-iff-w and its maximisers at the kinks A and B of E
-- statement:
--   Assume the standing assumptions. For the decision rule "exploit after $w$, not after $n$", the expected payoff of any experiment $\{\lambda_w,\lambda_n\}$ is
--   $$
--   V=p\lambda_w v_W+(1-p)(1-\lambda_n)v_N+\bigl((1-p)\lambda_n+p(1-\lambda_w)\bigr)v_S .
--   $$
--   Over the experiment set $\mathbf E$, this $V$ has a unique maximiser at a kink of the frontier: if $p>\hat p$, every $e\in\mathbf E$ other than the w-biased experiment $\{1,\lambda\}$ (point A of Figure 1) has strictly smaller $V$; if $p<\hat p$, every $e\in\mathbf E$ other than the n-biased experiment $\{\lambda,1\}$ (point B) has strictly smaller $V$.
--
--   This is the graphical argument of §2.2 that, for all but a degenerate case, the two biased experiments are the only ones optimally chosen.
--
--   **Formalization Note.** The rule is `id : Bool → Bool`. Experiments are compared by structure equality, i.e. equality of both precisions.
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), pp. 13–14 (PDF 14–15), §2.2, display V and Figure 1

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model

namespace ExpBias.OwnBias

theorem frontier_display_kink (P : Params) (hP : P.Standing) :
    (∀ e : Experiment, ruleValue P e id =
        P.p * e.lw * P.vW + (1 - P.p) * (1 - e.ln) * P.vN +
          ((1 - P.p) * e.ln + P.p * (1 - e.lw)) * P.vS) ∧
    (pHat P < P.p → ∀ e : Experiment, InE P e → e ≠ wBiased P →
        ruleValue P e id < ruleValue P (wBiased P) id) ∧
    (P.p < pHat P → ∀ e : Experiment, InE P e → e ≠ nBiased P →
        ruleValue P e id < ruleValue P (nBiased P) id) := by sorry

end ExpBias.OwnBias
