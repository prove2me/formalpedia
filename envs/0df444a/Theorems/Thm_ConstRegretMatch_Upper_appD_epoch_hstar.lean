-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_appD_epoch_hstar
-- name    : ConstRegretMatch.Upper.appD_epoch_hstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:50.763984+00:00
-- url     : https://prove2.me/theorems/01d8a1d7-2a06-43fe-b2bc-c7d1200c1e6f
-- title:
--   App. D, p. 49 — starting empty, 𝔼₀[h*(Q^{t_k})] = O(ϵ⁻¹) at every decision epoch k ≥ 1
-- statement:
--   Fix the topology of a matching network and match values $r>0$. There are constants $\kappa>0$ and $C\ge0$, depending only on the topology and $r$, such that the following holds. Let $\lambda$ be an arrival law under which the network satisfies GP with optimal solution $(z^*,s^*)$ and gap $\epsilon$, let $\theta$ be the dual vector of (SPP), and run the exhaustive resolving policy from the empty market with inter-action delay $\tau=\lceil\kappa\epsilon^{-1}\rceil$ and any resolving selection. Then
--   $$\mathbb E_{\mathbf 0}\big[h^*(Q^{t_k})\big]\le C\epsilon^{-1}\qquad\text{for all } k\ge1,$$
--   where $Q^{t_k}$ is the pre-match queue vector at the decision epoch $t_k=k\tau$.
--
--   This is the transient, all-epochs form of the queue bound: together with the dual weights $\theta_i>0$ on $\mathcal Q_0$ and the optimality test (Lemma 4.1), it yields the upper bound of Theorem 3.1.
--
--   **Formalization Note** The paper's $\mathcal O(\epsilon^{-1})$ is made explicit with $C$; $\kappa$ and $C$ are chosen before $\lambda$. $Q^{t_k}$ is the queue with the removals of $\mathcal Q_+$ leftovers (as in the paper's analysis); the expectation is over the first $k\tau$ arrivals. The paper's derivation of this display goes through Proposition 4.1 (9), which is not posed in this mission.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 49, App. D (Proof of the upper bound in Theorem 3.1)

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy
import Definitions.Def_ConstRegretMatch_Upper_Resolving

namespace ConstRegretMatch.Upper

/-- App. D, p. 49: there are constants `κ > 0` and `C ≥ 0`, depending only on the network and `r`,
such that under GP, with inter-action delay `τ = ⌈κ/ϵ⌉` and any tie-breaking selection for (3), the
exhaustive resolving policy started from the empty market has `𝔼₀[h*(Q^{t_k})] ≤ C/ϵ` at every
decision epoch `k ≥ 1`. -/
theorem appD_epoch_hstar {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : IsMatchValues r) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
      ∀ sel : (Fin n → ℕ) → Fin d → ℕ, IsResolvingSelection N r (Mzero z) sel →
      ∀ θ : Fin n → ℝ, IsSPPDual N r z s θ →
      ∀ k : ℕ, 1 ≤ k →
        expect lam (k * ⌈κ / gpGap z s⌉₊)
            (fun ω => hstar N z s θ (epochQueue N sel (Qplus s) ⌈κ / gpGap z s⌉₊ k ω))
          ≤ C / gpGap z s := by sorry

end ConstRegretMatch.Upper
