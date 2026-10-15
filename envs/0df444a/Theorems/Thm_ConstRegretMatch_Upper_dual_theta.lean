-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_dual_theta
-- name    : ConstRegretMatch.Upper.dual_theta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:56.26262+00:00
-- url     : https://prove2.me/theorems/6ee17321-5c19-4e9d-ab53-83913c5d7354
-- title:
--   §4.2, p. 20 — θ = Σ_{m∈ℳ₊} r_m y^m is the optimal dual of (SPP), θ ≥ 0, and θ_i > 0 for i ∈ 𝒬₀
-- statement:
--   Suppose the matching network satisfies GP with optimal solution $(z^*,s^*)$ of (SPP). Then:
--
--   1. the complementary-slackness system $\theta_j=0$ ($j\in\mathcal Q_+$), $\sum_iM_{im}\theta_i=r_m$ ($m\in\mathcal M_+$) has exactly one solution $\theta\in\mathbb R^n$;
--   2. this $\theta$ is the paper's
--   $$\theta_i=\Big(\sum_{m\in\mathcal M_+}r_my^m\Big)_i,\qquad i\in\mathcal A,$$
--   where $y^m$ are the rows of $Y=\mathcal B^{-1}$ (for every $Y$ with $Y\mathcal B=I$);
--   3. $\theta_i\ge0$ for every $i$;
--   4. $\theta$ is an optimal solution of the dual of (SPP): $\sum_iM_{im}\theta_i\ge r_m$ for every match $m$, and $\lambda\cdot\theta=r\cdot z^*$;
--   5. $\theta_i>0$ for every over-demanded type $i\in\mathcal Q_0$.
--
--   The dual weights $\theta$ are the weights of the Lyapunov function $h^*$, and their strict positivity on $\mathcal Q_0$ is what lets a bound on $h^*$ control every over-demanded queue.
--
--   **Formalization Note** The dual of (SPP) is $\min\{\lambda\cdot\theta: M^\top\theta\ge r,\ \theta\ge0\}$; item 4 states its optimality through dual feasibility and equality of the objective values. Item 5 is the paper's "uniqueness of $(z^*,s^*)$ implies $\theta_i>0$ for all $i\in\mathcal Q_0$".
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 20, §4.2

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP

namespace ConstRegretMatch.Upper

/-- §4.2, p. 20: under GP the complementary-slackness system `θᵀℬ = (r_{ℳ₊}, 0)` has exactly one
solution `θ`; it equals `∑_{m ∈ ℳ₊} r_m y^m` for the inverse `Y = ℬ⁻¹` with rows `y^m`; it is
nonnegative, it is an optimal solution of the dual of (SPP)
(`min λ · θ` s.t. `Mᵀθ ≥ r`, `θ ≥ 0`; dual feasible with `λ · θ = r · z*`), and `θ_i > 0` for
every over-demanded type `i ∈ 𝒬₀`. -/
theorem dual_theta {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ) (hr : IsMatchValues r)
    (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (hGP : IsGP N r lam z s) :
    (∃! θ : Fin n → ℝ, IsSPPDual N r z s θ) ∧
      ∀ θ : Fin n → ℝ, IsSPPDual N r z s θ →
        (∀ Y : Matrix (BasisIdx z s) (Fin n) ℝ, Y * basisMatrix N z s = 1 →
          ∀ i, θ i = ∑ m : {m // m ∈ Mplus z}, r m.1 * Y (Sum.inl m) i) ∧
        (∀ i, 0 ≤ θ i) ∧
        (∀ m, r m ≤ ∑ i, N.M i m * θ i) ∧
        ∑ i, lam i * θ i = ∑ m, r m * z m ∧
        ∀ i ∈ Qzero s, 0 < θ i := by sorry

end ConstRegretMatch.Upper
