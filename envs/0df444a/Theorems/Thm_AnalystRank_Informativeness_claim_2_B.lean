-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_2_B
-- name    : AnalystRank.Informativeness.claim_2_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:06.489726+00:00
-- url     : https://prove2.me/theorems/d22c0a98-7b5b-4126-9b36-eefcea0bdc29
-- title:
--   Claim 2 (B) — concave payoff (φ < 1): every monotonicity of Claim 2 (A.1)–(A.2) is reversed
-- statement:
--   Let $q\in(0,1)$, $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$ and $w_1>w_0>w_2$ with concave payoffs, $\varphi<1$. With the notation of Claim 2 (A):
--
--   1. in $\sigma^h\in[0,1]$, for fixed $\sigma^l$: $\Psi^h,\Psi^l$ are strictly decreasing, $\Delta U^h$ is strictly increasing and $\Delta U^l$ is strictly decreasing;
--   2. in $\sigma^l\in[0,1]$, for fixed $\sigma^h$: $\Psi^h,\Psi^l$ are strictly increasing, $\Delta U^l$ is strictly increasing and $\Delta U^h$ is strictly decreasing;
--   3. for $\sigma\in[0,1]^2$ with $\sigma^h>1-\sigma^l$, in $\rho\in[0,1]$: $\Psi^h$ is strictly decreasing, $\Psi^l$ is strictly increasing, and $\Delta U^h$ and $\Delta U^l$ are strictly increasing.
--
--   Under a concave payoff the ranking incentive pushes towards coordination rather than differentiation.
--
--   **Formalization Note** As in Claim 2 (A), the partial-derivative signs are stated as strict monotonicity on $[0,1]$, and the $\rho$-part is restricted to informative profiles $\sigma^h>1-\sigma^l$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 34, Claim 2 (B)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model
import Definitions.Def_AnalystRank_Informativeness_ClosedForms

namespace AnalystRank.Informativeness

open Set

theorem claim_2_B (q γ ρ w1 w0 w2 : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : phi w1 w0 w2 < 1) :
    (∀ σl ∈ Icc (0 : ℝ) 1,
      (∀ k : Bool, StrictAntiOn (fun x => Psi w1 w0 w2 γ ρ (x, σl) k) (Icc 0 1)) ∧
      StrictMonoOn (fun x => dU (rankPay w1 w0 w2) q γ ρ (x, σl) true) (Icc 0 1) ∧
      StrictAntiOn (fun x => dU (rankPay w1 w0 w2) q γ ρ (x, σl) false) (Icc 0 1)) ∧
    (∀ σh ∈ Icc (0 : ℝ) 1,
      (∀ k : Bool, StrictMonoOn (fun y => Psi w1 w0 w2 γ ρ (σh, y) k) (Icc 0 1)) ∧
      StrictMonoOn (fun y => dU (rankPay w1 w0 w2) q γ ρ (σh, y) false) (Icc 0 1) ∧
      StrictAntiOn (fun y => dU (rankPay w1 w0 w2) q γ ρ (σh, y) true) (Icc 0 1)) ∧
    (∀ σ : ℝ × ℝ, σ.1 ∈ Icc (0 : ℝ) 1 → σ.2 ∈ Icc (0 : ℝ) 1 → 1 - σ.2 < σ.1 →
      StrictAntiOn (fun r => Psi w1 w0 w2 γ r σ true) (Icc 0 1) ∧
      StrictMonoOn (fun r => Psi w1 w0 w2 γ r σ false) (Icc 0 1) ∧
      StrictMonoOn (fun r => dU (rankPay w1 w0 w2) q γ r σ true) (Icc 0 1) ∧
      StrictMonoOn (fun r => dU (rankPay w1 w0 w2) q γ r σ false) (Icc 0 1)) := by sorry

end AnalystRank.Informativeness
