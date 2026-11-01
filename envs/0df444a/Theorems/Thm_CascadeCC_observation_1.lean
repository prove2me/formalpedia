-- Prove2me | Theorems.Thm_CascadeCC_observation_1
-- name    : CascadeCC.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:03.571012+00:00
-- url     : https://prove2.me/theorems/69cb2280-1ae9-424f-84e9-206d2cc4c12a
-- title:
--   Observation 1 — the stopped sums of $\delta^v$, $\delta^\sigma$ are small (corrected: $O(\log k)$, not $0$)
-- statement:
--   Let $\hat\varphi>0$, $N\ge1$, and $\tau$ be the stopping time of the threshold $\hat\varphi$. Under the law of the Cascade Correction policy, for every product $j$,
--
--   $$
--   \Bigl|\mathbf E\Bigl[\sum_{t<\tau}\delta^v_{tj}\Bigr]\Bigr|\le\hat\varphi\bigl(1+\mathbf E[N-\tau]\bigr)+1,\qquad
--   \Bigl|\mathbf E\Bigl[\sum_{t<\tau}\delta^\sigma_{tj}\Bigr]\Bigr|\le Q\bigl(\hat\varphi(1+\mathbf E[N-\tau])+1\bigr).
--   $$
--
--   With Lemma EC.3 both are $O(\log k)$, which bounds the linear terms of the loss.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - correction: E[∑_{t<τ} δ^v_tj] = E[∑_{t<τ} δ^σ_tj] = 0, by the Stopping Time theorem → |E[∑_{t<τ} δ^v_tj]| ≤ φ̂(1 + E[N − τ]) + 1, and the same with factor Q for δ^σ; reason: ∑_{t<τ} δ_t is not a stopped martingale; counterexample: J = 1, N = 4, λ = u = 1, a = 1/4, large inventory, φ̂ = 1/8: δ₂ = 1/4 with probability 1/4 (τ = 2, sum 0), else δ₂ = −1/12 and |δ₃| = 1/4 (τ = 3, sum −1/12), so the mean is −1/16
--   - generalization: at a^D under Theorem 3's hypotheses → every a, every Y, every φ̂ > 0; reason: the proof uses only the martingale property and one-step sizes of δ
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Observation 1, p.ec12

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Observation 1, p.ec12 (SSRN abstract_id=3362921), corrected: |E[∑_{t<τ} δ^v_tj]| ≤ φ̂(1 + E[N − τ]) + 1,
and the same bound with factor Q for δ^σ_tj; with Lemma EC.3 these are O(log k), not 0.

**Formalization Note** The printed equalities E[∑_{t<τ} δ^v_tj] = E[∑_{t<τ} δ^σ_tj] = 0 are false, since
∑_{t<τ} δ_t is not a stopped martingale: with J = 1, N = 4, λ = u = 1, a = 1/4, large inventory and
φ̂ = 1/8 the mean is −1/16. It holds for every `a` and `Y`. -/
theorem observation_1 (M : Instance J) (a : Fin J → ℝ) (φ : ℝ) (hφ : 0 < φ) (N : ℕ) (hN : 1 ≤ N)
    (Y : Fin J → ℕ) (j : Fin J) :
    |ccExpect M N Y a (fun ω => sumBeforeTau M N Y a φ ω fun s => delta M N Y a ω s j)| ≤
        φ * (1 + ccExpect M N Y a (fun ω => (N : ℝ) - tau M N Y a φ ω)) + 1 ∧
      |ccExpect M N Y a (fun ω => sumBeforeTau M N Y a φ ω fun s =>
          arrivalDev M a (delta M N Y a ω s) j)| ≤
        Q M * (φ * (1 + ccExpect M N Y a (fun ω => (N : ℝ) - tau M N Y a φ ω)) + 1) := by sorry

end CascadeCC
