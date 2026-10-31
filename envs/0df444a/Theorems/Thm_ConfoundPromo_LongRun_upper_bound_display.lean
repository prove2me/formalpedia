-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_upper_bound_display
-- name    : ConfoundPromo.LongRun.upper_bound_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:35.307816+00:00
-- url     : https://prove2.me/theorems/32b35197-e8e8-43f4-85a5-1ea23f0411c9
-- title:
--   Proof of Theorem 1, p. OA–17 — for T > T̄, (1/T)W_T^{α,σ,π*}(µ) < co(W^C)(µ) + (5/4)ε uniformly in α, σ
-- statement:
--   Fix a market satisfying the standing assumptions, $\epsilon>0$ and $\mu\in[0,1]$. There is $\bar T$ such that for every $T>\bar T$, every signaling mechanism $\sigma$ with finitely many signals, every single-price promotion policy $\alpha$ based on the seller's belief ($\alpha\in\mathcal A^P\cap\mathcal A^M$, as fixed at the start of the proof, pp. OA–14–OA–15) and every myopic pricing policy $\pi^*$,
--   $$
--   \frac1T W_T^{\alpha,\sigma,\pi^*}(\mu)<co(W^C)(\mu)+\frac54\epsilon .
--   $$
--
--   This is the finite-horizon bound from which the upper half of Theorem 1 follows by letting $T\to\infty$ and then $\epsilon\to0$.
--
--   **Formalization Note.** $\bar T$ is chosen before $\sigma$, $\alpha$ and $\pi^*$, as the subsequent supremum over policies requires. The restriction to $\mathcal A^P\cap\mathcal A^M$ is the proof's own (it invokes Lemma 1 and Proposition 1 first); the bound for arbitrary $\alpha$ follows from it together with those two results.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA–17 (PDF 51), proof of Theorem 1, display after (32)

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- The upper-bound display (p. OA–17): for every ε > 0 and μ there is T̄, uniform over signals and
policies, such that (1/T) W_T^{α,σ,π*}(μ) < co(W^C)(μ) + (5/4)ε for all T > T̄. As in the proof
(§B.5.1–B.5.2, pp. OA–14, OA–15), the promotion policy is single-price and belief-based
(α ∈ A^P ∩ A^M) and the pricing policy is myopic. -/
theorem upper_bound_display (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Tbar : ℕ, ∀ T : ℕ, Tbar < T →
      ∀ (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsSinglePrice M α → IsBeliefBased M μ sig α →
        IsMyopic M μ sig α π →
        surplusT M μ sig α π / T < co (WC M) μ + 5 / 4 * ε := by sorry

end ConfoundPromo.LongRun
