-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_proposition_3
-- name    : ConfoundPromo.LongRun.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:33.022988+00:00
-- url     : https://prove2.me/theorems/adc49344-816b-48b5-ace6-bfe884dac40b
-- title:
--   Proposition 3, p. 18 — A^C(µ) is non-empty for every belief µ ∈ [0, 1]
-- statement:
--   Fix a market satisfying the standing assumptions, a horizon $T\ge1$ and a belief $\mu\in[0,1]$, and let the seller start from belief $\mu$ with no further signal. There are a promotion policy $\alpha$, single-price and belief-based, and a myopic pricing policy $\pi^*$ against it, such that $\alpha$ is confounding: along every outcome path of positive probability the seller's belief stays equal to $\mu$ in every period,
--   $$
--   \mathbb P(\mu_{t+1}=\mu\mid\mu_t=\mu,\pi^*,\alpha)=1,\qquad t=1,\dots,T .
--   $$
--   That is, $\mathcal A^C(\mu)\neq\emptyset$: whatever the seller's belief, the platform can keep it from moving.
--
--   **Formalization Note.** The absence of a signal is encoded by the one-signal mechanism. A myopic pricing policy is required at every history, including those off the equilibrium path.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. 18, Proposition 3

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Proposition 3 (p. 18): for every belief μ and horizon T there is a confounding promotion policy
(belief-based, single-price) with a myopic pricing response. -/
theorem proposition_3 (M : Market) (hM : M.Standing) (T : ℕ) (hT : 0 < T)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (α : Promo 1 T) (π : Pricing 1 T), α.IsValid ∧ IsBeliefBased M μ trivialSignal α ∧
      IsSinglePrice M α ∧ IsMyopic M μ trivialSignal α π ∧
      IsConfounding M μ trivialSignal α π := by sorry

end ConfoundPromo.LongRun
