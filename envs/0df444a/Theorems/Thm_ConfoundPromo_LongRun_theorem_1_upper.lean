-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_theorem_1_upper
-- name    : ConfoundPromo.LongRun.theorem_1_upper
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T08:34:35.778046+00:00
-- url     : https://prove2.me/theorems/d56963f3-79d2-4ad3-ba93-e45c0f707f50
-- title:
--   Theorem 1, p. 19 (upper bound) — under myopic pricing, the long-run average consumer surplus of any signal and promotion policy is at most co(W^C)(µ0) + ε
-- statement:
--   Fix a market satisfying the standing assumptions (Assumptions 1 and 2) and a prior $\mu_0\in[0,1]$, and let the seller price myopically (Definition 1). Let $W^C(\mu)$ be the maximal one-period consumer surplus of a confounding promotion rule at belief $\mu$, as in (10), and $co(W^C)$ its concavification. Then for every $\varepsilon>0$ there is $T_0$ such that for all horizons $T\ge T_0$, every signaling mechanism $\sigma$ (with finitely many signals), every promotion policy $\alpha$ and every myopic pricing policy $\pi^*$,
--   $$
--   \frac1T\,W_T^{\alpha,\sigma,\pi^*}(\mu_0)\le co(W^C)(\mu_0)+\varepsilon .
--   $$
--   Equivalently, $\limsup_{T\to\infty}\sup_{\alpha,\sigma}\frac1T W_T^{\alpha,\sigma,\pi^*}(\mu_0)\le co(W^C)(\mu_0)$.
--
--   This is the upper-bound half of Theorem 1: in the long run the platform cannot beat the concavified best confounding surplus. Together with the existence half (a signal and a confounding policy attaining $co(W^C)(\mu_0)$ for every horizon), it gives the limit in Theorem 1.
--
--   **Formalization Note.** The statement is part (i) of the platform's formal Theorem 1, verbatim. No single-price or belief-based restriction is imposed on the promotion policy; the paper reaches such policies through Lemma 1 and Proposition 1.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. 19, Theorem 1 (the bound lim sup_T sup_{α,σ} (1/T) W_T ≤ co(W^C)(µ0)); proof in §B.5.2, pp. OA-15 to OA-17

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Theorem 1 (p. 19), upper-bound half: for every ε > 0 there is T₀ such that for all T ≥ T₀ the
average consumer surplus of any valid signal, any valid promotion policy and any myopic pricing
policy is at most co(W^C)(μ0) + ε. -/
theorem theorem_1_upper (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → 0 < T →
      ∀ (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsMyopic M μ0 sig α π →
        surplusT M μ0 sig α π / T ≤ co (WC M) μ0 + ε := by sorry

end ConfoundPromo.LongRun
