-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_optimal_signal
-- name    : ConfoundPromo.LongRun.optimal_signal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:42.108255+00:00
-- url     : https://prove2.me/theorems/0db77198-4f1c-4d9a-9e30-e06a03cae5ec
-- title:
--   Proof of Theorem 1, p. OA–17, Existence of Optimal Signaling Mechanism — a two-signal σ with E[W^C(µ_1)] = co(W^C)(µ0)
-- statement:
--   Fix a market satisfying the standing assumptions and a prior $\mu_0\in[0,1]$. There is a signaling mechanism $\sigma$ with two signals such that, writing $\mathbb P(s)=\mu_0\sigma(s\mid\phi_H)+(1-\mu_0)\sigma(s\mid\phi_L)$ and $\mu_1(s)$ for the Bayes posterior after $s$,
--   $$
--   \sum_{s}\mathbb P(s)\,W^C(\mu_1(s))=co(W^C)(\mu_0).
--   $$
--
--   This is the Kamenica–Gentzkow step of the proof of Theorem 1: the platform splits the prior into posteriors at which the concave envelope of $W^C$ is attained.
--
--   **Formalization Note.** The posterior of a signal of probability $0$ is set to $\mu_0$; it carries no weight. The page derives existence from upper semicontinuity of $W^C$ "by the proof of Lemma 4".
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA–17 (PDF 51), proof of Theorem 1, "Existence of Optimal Signaling Mechanism"

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- "Existence of Optimal Signaling Mechanism" (p. OA–17): a two-signal mechanism whose posteriors
μ_1(s) satisfy ∑_s P(s) W^C(μ_1(s)) = co(W^C)(μ0). -/
theorem optimal_signal (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ sig : Signal 2, sig.IsValid ∧
      ∑ s, (μ0 * sig true s + (1 - μ0) * sig false s) *
          WC M (bayes μ0 (sig true s) (sig false s)) = co (WC M) μ0 := by sorry

end ConfoundPromo.LongRun
