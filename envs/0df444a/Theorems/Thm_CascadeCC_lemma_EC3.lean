-- Prove2me | Theorems.Thm_CascadeCC_lemma_EC3
-- name    : CascadeCC.lemma_EC3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:39.650595+00:00
-- url     : https://prove2.me/theorems/a84dae49-5077-4e26-8db1-23bfd51a65f5
-- title:
--   Lemma EC.3 — $\mathbf E[k-\tau^k]\le 1+\Psi\log k$
-- statement:
--   For every threshold $\hat\varphi>0$ there is $\Psi>0$ such that, for every horizon $N\ge1$ and inventory $Y$, the stopping time $\tau$ of the threshold under the law of the Cascade Correction policy satisfies
--
--   $$
--   \mathbf E[N-\tau]\ \le\ 1+\Psi\log N .
--   $$
--
--   So the correction leaves the safe region only in the last $O(\log N)$ periods, in expectation.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - encoding: k with T = 1, O in log k → N with the bound in log N; reason: the WLOG T = 1 is not used, and log N = log k + log T
--   - generalization: the threshold φ̂ of the proof, at a^D → every φ̂ > 0, every a, every Y, with Ψ depending on the instance and φ̂ only; reason: the proof uses only the martingale property
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Lemma EC.3, p.ec11

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Lemma EC.3, p.ec11 (SSRN abstract_id=3362921): there exists Ψ > 0, independent of k, with
E[k − τ^k] ≤ 1 + Ψ log k, in the form E[N − τ] ≤ 1 + Ψ log N, for every threshold φ̂ > 0.

**Formalization Note** N is the scaled horizon, so that the paper's T = 1 reduction is not needed; a bound in
log N is a bound in log k since N = kT. It holds for every `a` and `Y`, and Ψ depends on `M` and φ̂ only. -/
theorem lemma_EC3 (M : Instance J) (a : Fin J → ℝ) (φ : ℝ) (hφ : 0 < φ) :
    ∃ Ψ : ℝ, 0 < Ψ ∧ ∀ (N : ℕ) (Y : Fin J → ℕ), 1 ≤ N →
      ccExpect M N Y a (fun ω => (N : ℝ) - tau M N Y a φ ω) ≤ 1 + Ψ * Real.log N := by sorry

end CascadeCC
