-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_lemma_1
-- name    : ConfoundPromo.LongRun.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:21.707981+00:00
-- url     : https://prove2.me/theorems/dd9e3927-01c0-4985-b517-89d816ac5975
-- title:
--   Lemma 1, p. 13 — under myopic pricing, a promotion policy depending on histories only through beliefs is without loss
-- statement:
--   Fix a market satisfying the standing assumptions, a prior $\mu_0\in[0,1]$, a horizon $T$, a signaling mechanism $\sigma$ with finitely many signals and a promotion policy $\alpha$, and let the seller follow a myopic Bayesian pricing policy $\pi^*$ (Definition 1). Then there are a promotion policy $\alpha'$ that depends on the history only through the seller's belief (Definition 2) and a myopic pricing policy $\pi'$ against $\alpha'$ such that
--   $$
--   W_T^{\alpha,\sigma,\pi^*}(\mu_0)\le W_T^{\alpha',\sigma,\pi'}(\mu_0).
--   $$
--
--   The lemma reduces the platform's design problem to policies whose state is the seller's belief.
--
--   **Formalization Note.** Definition 2 says "for all $\sigma\in\Sigma$"; here belief-basedness is required for the given $\sigma$, the one used in the payoff. The myopic policy against $\alpha'$ is exhibited, as Definition 1 allows several myopic policies when ties remain.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. 13, Lemma 1

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Lemma 1 (p. 13): under myopic pricing, any promotion policy is weakly improved by one that
depends on histories only through the seller's belief (Definition 2, for the given signal). -/
theorem lemma_1 (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1)
    (T n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T)
    (hsig : sig.IsValid) (hα : α.IsValid) (hπ : IsMyopic M μ0 sig α π) :
    ∃ (α' : Promo n T) (π' : Pricing n T), α'.IsValid ∧ IsBeliefBased M μ0 sig α' ∧
      IsMyopic M μ0 sig α' π' ∧ surplusT M μ0 sig α π ≤ surplusT M μ0 sig α' π' := by sorry

end ConfoundPromo.LongRun
