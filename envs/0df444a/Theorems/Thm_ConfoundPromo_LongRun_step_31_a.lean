-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_step_31_a
-- name    : ConfoundPromo.LongRun.step_31_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:30.151985+00:00
-- url     : https://prove2.me/theorems/3caca5bc-02c0-4c8d-bc3d-1482230d8dcb
-- title:
--   (31)(a), p. OA–16 — co(W^C) is concave, beliefs are a martingale, and E[co(W^C)(µ_t)] ≤ co(W^C)(µ0)
-- statement:
--   Fix a market satisfying the standing assumptions. Then $co(W^C)$ is concave on $[0,1]$. Moreover, for every prior $\mu_0\in[0,1]$, horizon $T$, signaling mechanism, promotion policy and myopic pricing policy, and every period $t=1,\dots,T+1$, the seller's belief $\mu_t$ satisfies, with $\mathbb E_Z$ the expectation over $\phi$, the signal and the sale outcomes,
--   $$
--   \mathbb E_Z[\mu_t]=\mu_0,\qquad \mathbb E_Z\big[co(W^C)(\mu_t)\big]\le co(W^C)(\mu_0).
--   $$
--
--   The first identity is the martingale property of Bayesian beliefs; the inequality is Jensen's inequality for the concave function $co(W^C)$. This is step (a) of (31) in the proof of Theorem 1.
--
--   **Formalization Note.** The Lean belief index $t=0,\dots,T$ is the paper's period $t+1$, so $\mu_1$ (after the signal) through $\mu_{T+1}$ are covered.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA–16 (PDF 50), proof of Theorem 1, step (a) of (31)

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Step (a) of (31) (p. OA–16): co(W^C) is concave on [0, 1]; under myopic pricing the beliefs
are a martingale, E_Z[μ_t] = μ0; and E_Z[co(W^C)(μ_t)] ≤ co(W^C)(μ0). Lean belief index t is the
paper's μ_{t+1}, for t = 0, …, T. -/
theorem step_31_a (M : Market) (hM : M.Standing) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (co (WC M)) ∧
    ∀ (μ0 : ℝ), μ0 ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (T n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsMyopic M μ0 sig α π → ∀ t : ℕ, t ≤ T →
          expect M μ0 sig α π (fun _ s y => belief M μ0 sig α t (histAt π s y t)) = μ0 ∧
          expect M μ0 sig α π (fun _ s y => co (WC M) (belief M μ0 sig α t (histAt π s y t)))
            ≤ co (WC M) μ0 := by sorry

end ConfoundPromo.LongRun
