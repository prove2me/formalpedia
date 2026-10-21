-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_2_A
-- name    : AnalystRank.Informativeness.claim_2_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:05.325558+00:00
-- url     : https://prove2.me/theorems/0b85ddbe-0e48-4b32-a68f-5c0b73da6a03
-- title:
--   Claim 2 (A) — convex payoff: Ψ rises in σʰ and falls in σˡ, ΔUʰ falls in σʰ and rises in σˡ, ΔUˡ the reverse; on σʰ > 1 − σˡ, Ψʰ↑, Ψˡ↓, ΔU↓ in ρ
-- statement:
--   Let $q\in(0,1)$, $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$ and $w_1>w_0>w_2$ with convex payoffs, $\varphi>1$. Write $\Delta U^h(\sigma^h,\sigma^l)$ and $\Delta U^l(\sigma^h,\sigma^l)$ for the rank-game net payoffs of a truthful forecast when the other analyst plays $(\sigma^h,\sigma^l)$, and $\Psi^h,\Psi^l$ for the ratios (A.7) of the state-conditional net payoffs.
--
--   1. **(A.1)** In $\sigma^h\in[0,1]$, for fixed $\sigma^l\in[0,1]$: $\Psi^h$ and $\Psi^l$ are strictly increasing, $\Delta U^h$ is strictly decreasing and $\Delta U^l$ is strictly increasing. In $\sigma^l\in[0,1]$, for fixed $\sigma^h\in[0,1]$: $\Psi^h$ and $\Psi^l$ are strictly decreasing, $\Delta U^l$ is strictly decreasing and $\Delta U^h$ is strictly increasing.
--   2. **(A.2)** For every informative profile, $\sigma\in[0,1]^2$ with $\sigma^h>1-\sigma^l$, as functions of the correlation $\rho\in[0,1]$: $\Psi^h$ is strictly increasing, $\Psi^l$ is strictly decreasing, and both $\Delta U^h$ and $\Delta U^l$ are strictly decreasing.
--
--   In words, under a convex payoff an analyst's incentive to forecast truthfully weakens as the other analyst forecasts the same signal more often, and weakens as the signals become more correlated.
--
--   **Formalization Note** The paper states these as signs of partial derivatives. All the functions involved are affine or ratios of affine functions, so the signs are stated as strict monotonicity on $[0,1]$. Part (A.2) is restricted to $\sigma^h>1-\sigma^l$, as in its proof ("For any informative equilibrium"): on the pooling line $\sigma^h=1-\sigma^l$ the payoffs do not depend on $\rho$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 34, Claim 2 (A.1)–(A.2)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model
import Definitions.Def_AnalystRank_Informativeness_ClosedForms

namespace AnalystRank.Informativeness

open Set

theorem claim_2_A (q γ ρ w1 w0 w2 : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : 1 < phi w1 w0 w2) :
    (∀ σl ∈ Icc (0 : ℝ) 1,
      (∀ k : Bool, StrictMonoOn (fun x => Psi w1 w0 w2 γ ρ (x, σl) k) (Icc 0 1)) ∧
      StrictAntiOn (fun x => dU (rankPay w1 w0 w2) q γ ρ (x, σl) true) (Icc 0 1) ∧
      StrictMonoOn (fun x => dU (rankPay w1 w0 w2) q γ ρ (x, σl) false) (Icc 0 1)) ∧
    (∀ σh ∈ Icc (0 : ℝ) 1,
      (∀ k : Bool, StrictAntiOn (fun y => Psi w1 w0 w2 γ ρ (σh, y) k) (Icc 0 1)) ∧
      StrictAntiOn (fun y => dU (rankPay w1 w0 w2) q γ ρ (σh, y) false) (Icc 0 1) ∧
      StrictMonoOn (fun y => dU (rankPay w1 w0 w2) q γ ρ (σh, y) true) (Icc 0 1)) ∧
    (∀ σ : ℝ × ℝ, σ.1 ∈ Icc (0 : ℝ) 1 → σ.2 ∈ Icc (0 : ℝ) 1 → 1 - σ.2 < σ.1 →
      StrictMonoOn (fun r => Psi w1 w0 w2 γ r σ true) (Icc 0 1) ∧
      StrictAntiOn (fun r => Psi w1 w0 w2 γ r σ false) (Icc 0 1) ∧
      StrictAntiOn (fun r => dU (rankPay w1 w0 w2) q γ r σ true) (Icc 0 1) ∧
      StrictAntiOn (fun r => dU (rankPay w1 w0 w2) q γ r σ false) (Icc 0 1)) := by sorry

end AnalystRank.Informativeness
