-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_eq_11_stationary
-- name    : ConstRegretMatch.Upper.eq_11_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:34:40.780985+00:00
-- url     : https://prove2.me/theorems/0be03dd3-c694-4c12-b19c-93104b1822d0
-- title:
--   (11), p. 23 — under the stationary distribution π of the epoch chain with τ = ⌈κϵ⁻¹⌉, 𝔼_π[h*(Q⁰)] = O(ϵ⁻¹)
-- statement:
--   Fix the topology of a matching network and match values $r>0$. There are constants $\kappa>0$ and $C\ge0$, depending only on the topology and $r$, such that the following holds. Let $\lambda$ be an arrival law under which the network satisfies GP with optimal solution $(z^*,s^*)$ and gap $\epsilon$, let $\theta$ be the dual vector of (SPP), and run the exhaustive resolving policy with inter-action delay $\tau=\lceil\kappa\epsilon^{-1}\rceil$ and any resolving selection. Then every stationary distribution $\pi$ of the epoch chain $(Q^{t_k},k\in\mathbb N)$ has $h^*$ integrable and
--   $$\mathbb E_\pi\big[h^*(Q^0)\big]\le C\epsilon^{-1},\qquad Q^0\sim\pi. \tag{11}$$
--
--   This is the stationary version of the queue bound behind Theorem 3.1: since $\theta_i>0$ on $\mathcal Q_0$, it bounds the stationary mean of every over-demanded queue at the decision epochs by a multiple of $\epsilon^{-1}$.
--
--   **Formalization Note** The paper's $\mathcal O(\epsilon^{-1})$ is made explicit with $C$, and $\kappa$ and $C$ are chosen before $\lambda$, so they are uniform in it. The paper speaks of "the unique stationary distribution"; the statement is made for every stationary distribution, which says the same when it is unique and does not assume its existence. The paper derives (11) from (10) and Proposition 4.1 (9); those are not posed in this mission.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 23, display (11)

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy
import Definitions.Def_ConstRegretMatch_Upper_Resolving
import Definitions.Def_ConstRegretMatch_Upper_EpochKernel

namespace ConstRegretMatch.Upper

open MeasureTheory ProbabilityTheory

/-- (11), p. 23: there are constants `κ > 0` and `C ≥ 0`, depending only on the network and `r`,
such that under GP, with inter-action delay `τ = ⌈κ/ϵ⌉` and any tie-breaking selection for (3),
every stationary distribution `π` of the epoch chain `(Q^{t_k}, k ∈ ℕ)` of the exhaustive resolving
policy has `h*` integrable and `𝔼_π[h*(Q⁰)] ≤ C/ϵ`. -/
theorem eq_11_stationary {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : IsMatchValues r) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
      ∀ sel : (Fin n → ℕ) → Fin d → ℕ, IsResolvingSelection N r (Mzero z) sel →
      ∀ θ : Fin n → ℝ, IsSPPDual N r z s θ →
      ∀ π : Measure (Fin n → ℕ), IsProbabilityMeasure π →
        (epochKernel N lam sel (Qplus s) ⌈κ / gpGap z s⌉₊).Invariant π →
          Integrable (hstar N z s θ) π ∧ ∫ q, hstar N z s θ q ∂π ≤ C / gpGap z s := by sorry

end ConstRegretMatch.Upper
