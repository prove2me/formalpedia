-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_theorem_1
-- name    : ConfoundPromo.LongRun.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:32.017837+00:00
-- url     : https://prove2.me/theorems/f741b35f-c7b3-44a2-84e1-62cb919156a9
-- title:
--   Theorem 1, p. 19 — the long-run average optimal consumer surplus under myopic pricing is co(W^C)(µ), attained for every T by a signal and a confounding policy
-- statement:
--   Fix a market satisfying the standing assumptions (Assumptions 1 and 2) and a prior $\mu_0\in[0,1]$, and let the seller price myopically ($\pi^*$, Definition 1). Let $W^C(\mu)$ be the maximal one-period consumer surplus of a confounding promotion policy at belief $\mu$, as in (10), and $co(W^C)$ its concavification. Then
--   $$
--   \lim_{T\to\infty}\ \sup_{\alpha\in\mathcal A,\ \sigma\in\Sigma}\ \frac1T W_T^{\alpha,\sigma,\pi^*}(\mu_0)=co(W^C)(\mu_0).
--   $$
--   Furthermore, for every horizon $T$ there are a signaling mechanism $\sigma$ and a confounding promotion policy $\alpha$ that generate an expected average consumer surplus of exactly $co(W^C)(\mu_0)$.
--
--   In words, the platform cannot do better in the long run than confounding the seller's learning after an initial signal, and this combination is optimal for every horizon.
--
--   **Formalization Note.** The limit is stated as two halves. (i) For every $\epsilon>0$ there is $T_0$ such that for all $T\ge T_0$, every signaling mechanism with finitely many signals, every promotion policy and every myopic pricing policy, the average surplus is at most $co(W^C)(\mu_0)+\epsilon$. (ii) For every $T\ge1$ there are a finite signaling mechanism, a belief-based confounding promotion policy and a myopic pricing policy with average surplus exactly $co(W^C)(\mu_0)$. Together they give the limit, including its existence. Signal sets are finite (`Fin n`), pricing policies deterministic, and only policies admitting a myopic response are considered, which the paper presumes. In (ii) the myopic pricing policy is exhibited, the reading of the paper's fixed selection $\pi^*$.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. 19, Theorem 1

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Theorem 1 (p. 19): lim_{T→∞} sup_{α,σ} (1/T) W_T^{α,σ,π*}(μ0) = co(W^C)(μ0), as (i) a uniform
ε–T₀ upper bound over all valid signals, promotion policies and myopic pricing policies, and (ii)
for every T exact attainment by a signal and a belief-based confounding policy. -/
theorem theorem_1 (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → 0 < T →
      ∀ (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsMyopic M μ0 sig α π →
        surplusT M μ0 sig α π / T ≤ co (WC M) μ0 + ε) ∧
    (∀ T : ℕ, 0 < T → ∃ (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
      sig.IsValid ∧ α.IsValid ∧ IsBeliefBased M μ0 sig α ∧ IsMyopic M μ0 sig α π ∧
      IsConfounding M μ0 sig α π ∧ surplusT M μ0 sig α π / T = co (WC M) μ0) := by sorry

end ConfoundPromo.LongRun
