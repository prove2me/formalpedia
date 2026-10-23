-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_lemma_2
-- name    : ConfoundPromo.LongRun.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:24.795986+00:00
-- url     : https://prove2.me/theorems/280fff62-0cc1-41aa-a09b-598a586d50e9
-- title:
--   Lemma 2, p. OA–15 — surplus above co(W^C)(µ) + ε forces the purchase probabilities under φ_H and φ_L apart by δ(ε)
-- statement:
--   Fix a market satisfying the standing assumptions and $\epsilon>0$. There is $\delta=\delta(\epsilon)>0$ with the following property. Let $\mu\in[0,1]$ be a belief, let $\alpha_t(\cdot,\phi)$ be a single-price promotion rule with values in $[0,1]$, and let $p_t$ be a myopic price against it at belief $\mu$ (Definition 1). If the current expected consumer surplus exceeds $co(W^C)(\mu)+\epsilon$, that is $\mu\in M^{\alpha_t}(\epsilon)$, then
--   $$
--   \big|\phi_H\alpha_t(p_t,\phi_H)\bar\rho_0(p_t)+(1-\phi_H)\bar\rho_c(p_t)-\phi_L\alpha_t(p_t,\phi_L)\bar\rho_0(p_t)-(1-\phi_L)\bar\rho_c(p_t)\big|>\delta .
--   $$
--
--   A period whose surplus beats the concavified confounding value is therefore informative for the seller, by an amount that does not depend on the belief or the rule.
--
--   **Formalization Note.** The lemma is stated for a single period, since $M^{\alpha_t}(\epsilon)$ depends on the policy only through the current rule at the current belief. $\delta$ is chosen before $\mu$ and the rule.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA–15 (PDF 49), Lemma 2

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Lemma 2 (p. OA–15), one-period form: there is δ(ε) > 0, uniform in the belief and the rule,
such that a single-price rule whose myopic outcome yields current surplus above co(W^C)(μ) + ε
separates the purchase probabilities under φ_H and φ_L by more than δ. -/
theorem lemma_2 (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∀ (a : ℝ → Bool → ℝ) (p : ℝ),
      IsValidRule a →
      (∃ pbar ∈ M.price, ∀ q ∈ M.price, q ≠ pbar → ∀ b, a q b = 0) →
      IsMyopicChoice M μ a p →
      co (WC M) μ + ε < expSurplus M μ a p →
      δ < |saleProb M true (a p true) p - saleProb M false (a p false) p| := by sorry

end ConfoundPromo.LongRun
