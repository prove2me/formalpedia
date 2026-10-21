-- Prove2me | Theorems.Thm_BatchTesting_PTAS_lemma_2
-- name    : BatchTesting.PTAS.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:48.138987+00:00
-- url     : https://prove2.me/theorems/4b37315a-90e7-4881-9e9d-54d2f7f23cc1
-- title:
--   Lemma 2, p. 14 — the §3.4 actions cost at most $(1+\epsilon)\,C(\Delta^{*(t)})$
-- statement:
--   In the setting of Lemma 1 — an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, $0<\epsilon\le1$, a path $N^{*(0)},\dots,N^{*(T)}$ of the dynamic program over $F$, and the §3.4 sequence $N^{(0)},\dots,N^{(T)}$ built from it — the actions satisfy
--
--   $$C\big(N^{(t)}-N^{(t-1)}\big)\ \le\ (1+\epsilon)\cdot C\big(N^{*(t)}-N^{*(t-1)}\big)\qquad\text{for every }1\le t\le T,$$
--
--   where $C(\Delta)=\beta/c_{\min}+\sum_r\Delta_r(1+\epsilon)^r$.
--
--   Exhausting the classes at least $\kappa$ below the most expensive class touched costs at most $\epsilon$ times that class's cost; this is the per-step charge of Theorem 2.
--
--   **Formalization Note.** $N^{(t)}-N^{(t-1)}$ is the action $\Delta^{(t)}$ of §3.4 (coordinatewise; the sequence is non-decreasing). $\beta\ge0$ is used.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 14, §3.4, Lemma 2

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem lemma_2 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (F I eps) πs) :
    ∀ t, t + 1 < πs.length →
      stepCost I eps ((niceSeq I eps πs).getD (t + 1) 0 - (niceSeq I eps πs).getD t 0) ≤
        (1 + eps) * stepCost I eps (πs.getD (t + 1) 0 - πs.getD t 0) := by sorry

end BatchTesting.PTAS
