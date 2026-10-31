-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_proposition_1
-- name    : ConfoundPromo.LongRun.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:29.906205+00:00
-- url     : https://prove2.me/theorems/d3a90b83-1f27-4c16-87cd-898becc1fbc2
-- title:
--   Proposition 1, p. 14 — single-price, belief-based promotion with two signals is without loss under myopic pricing
-- statement:
--   Fix a market satisfying the standing assumptions, a prior $\mu_0\in[0,1]$, a horizon $T\ge 1$, a signaling mechanism $\sigma$ with finitely many signals and a promotion policy $\alpha$, and let the seller price myopically ($\pi^*$, Definition 1). Then there are a simple signaling mechanism $\sigma'$ with two signals, a promotion policy $\alpha'$ that is single-price (Definition 3) and belief-based (Definition 2), and a myopic pricing policy $\pi'$ against $(\sigma',\alpha')$, such that
--   $$
--   W_T^{\alpha,\sigma,\pi^*}(\mu_0)\le W_T^{\alpha',\sigma',\pi'}(\mu_0).
--   $$
--
--   Together with Lemma 1 this lets the proof of Theorem 1 restrict attention to single-price promotion policies.
--
--   **Formalization Note.** The page reads "there exists $\alpha'$, $\sigma'$ such that for all $\mu_0\in[0,1]$". Here $\mu_0$ is fixed before $\alpha',\sigma'$ are chosen, because the construction in §B.2 builds $\alpha'$ from the myopic prices, which depend on $\mu_0$ through the beliefs. The two signals are `Fin 2`.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. 14, Proposition 1

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Proposition 1 (p. 14), with the prior fixed before the existential: under myopic pricing,
any (σ, α) is weakly improved by a two-signal mechanism and a single-price, belief-based policy. -/
theorem proposition_1 (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T) (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T)
    (hsig : sig.IsValid) (hα : α.IsValid) (hπ : IsMyopic M μ0 sig α π) :
    ∃ (sig' : Signal 2) (α' : Promo 2 T) (π' : Pricing 2 T), sig'.IsValid ∧ α'.IsValid ∧
      IsSinglePrice M α' ∧ IsBeliefBased M μ0 sig' α' ∧ IsMyopic M μ0 sig' α' π' ∧
      surplusT M μ0 sig α π ≤ surplusT M μ0 sig' α' π' := by sorry

end ConfoundPromo.LongRun
