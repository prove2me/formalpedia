-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_lemma_4
-- name    : BreakingSample.Perturbed.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:13.365711+00:00
-- url     : https://prove2.me/theorems/c27099a8-24bd-4826-b22f-740fe6e3adbb
-- title:
--   Lemma 4 — separated empirical policy survives absorbing-grid replacement
-- statement:
--   Suppose $\omega>0$ and the optimal action values of an empirical MDP have a gap of at least $\omega$ at every state. For each pair $(s,a)$, there is a grid point $u_0\in\mathcal N_{(1-\gamma)\omega/4}$ such that the original optimal policy is the unique optimal policy of the $(s,a)$-absorbing MDP with reward $u_0$:
--
--   $$\widehat\pi^\star=\widehat\pi^\star_{s,a,u_0}.$$
--
--   The grid representation is the policy-stability step used in the leave-one-row-out argument.
--
--   **Formalization Note** The deterministic statement applies to any transition kernel. It states uniqueness, not merely optimality, for the absorbing model.
-- source:
--   arXiv:2005.12900v8, Lemma 4, (41)–(43), p. 16

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Absorbing

namespace BreakingSample.Perturbed

/-- Lemma 4 and (43), arXiv:2005.12900v8, p. 16. -/
theorem lemma_4 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (Phat : S → A → S → ℝ) (r : S → A → ℝ) (γ ω : ℝ)
    (hM : IsDiscountedMDP Phat r γ) (hω : 0 < ω) (hSep : IsSeparated Phat r γ ω) :
    ∀ s a, ∃ u₀ ∈ epsNet γ ((1 - γ) * ω / 4),
      ∀ π : S → A, IsOptimal Phat r γ π →
        IsOptimal (absorbKernel Phat s a) (absorbReward r s a u₀) γ π ∧
        ∀ π' : S → A, IsOptimal (absorbKernel Phat s a) (absorbReward r s a u₀) γ π' →
          π' = π := by sorry

end BreakingSample.Perturbed
