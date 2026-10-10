-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicFiniteHorizonOptimalPolicy_fundamental
-- name    : ActuarialValuation.finiteEntropicFiniteHorizonOptimalPolicy_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:53:42.676049+00:00
-- url     : https://prove2.me/theorems/5b8a9a15-950f-4e57-b4fc-4817528317b9
-- title:
--   Finite-horizon risk-sensitive actuarial retention control fundamental theorem
-- statement:
--   The complete finite-horizon cost-minimisation claim is the conjunction of two distinct mathematical statements: every deterministic nonstationary Markov policy has entropic cost at least the Bellman optimum at every starting state, and one such policy attains the optimum for all starting states. The insurer's annual cost includes its cashflows and discounted continuation within the same conditional entropic valuation.
--
--   **Mathematical statement**
--
--   $$
--   \forall\pi,s,\ V_n(s)\le J^\pi_n(s),\quad\exists\pi^*,\ \forall s,\ J^{\pi^*}_n(s)=V_n(s)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
import Definitions.Def_actuarial_finiteEntropicPolicyValue

namespace ActuarialValuation

theorem finiteEntropicFiniteHorizonOptimalPolicy_fundamental {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (n : ℕ)
  (hP : ∀ s a t, 0 ≤ P s a t)
  (hsum : ∀ s a, (∑ t : S, P s a t) = 1)
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma) :
  (∀ (policy : ℕ → S → A) (s : S),
    finiteEntropicBellmanValue P cost beta gamma terminal n s ≤
      finiteEntropicPolicyValue P cost beta gamma terminal policy n s)
  ∧ (∃ policy : ℕ → S → A, ∀ s : S,
      finiteEntropicPolicyValue P cost beta gamma terminal policy n s =
        finiteEntropicBellmanValue P cost beta gamma terminal n s) := by sorry

end ActuarialValuation
