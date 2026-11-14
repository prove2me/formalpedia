-- Prove2me | Theorems.Thm_AltRegret_lemma_1
-- name    : AltRegret.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T00:06:20.872199+00:00
-- url     : https://prove2.me/theorems/2d8296fc-3326-4e5f-8ccb-5d2e76a6c404
-- title:
--   Lemma 1 — $\theta_t$ is the unique maximizer, $\theta_t=\sum_i p_{t,i}c_{t-1,i}$, and $x_t\in\Delta_d$ (corrected: $\beta>0$)
-- statement:
--   Consider the alternation-aware Hedge algorithm with parameters $\eta\in\mathbb R$ and $\beta$, where
--   $$
--   0<\beta<\tfrac12 .
--   $$
--   Let $d\ge1$, let $t\ge1$ be a round, and let the losses satisfy $c_{t-1}\in[-1,1]^d$ (with $c_0=\mathbf 0$). Write
--   $$
--   F_t(\theta)=\log\sum_{i=1}^{d}\exp\!\big[-\eta L_{t-1,i}-\beta(c_{t-1,i}-\theta)^2\big].
--   $$
--   Then:
--
--   1. $F_t$ has exactly one maximizer over $\theta\in\mathbb R$;
--   2. the algorithm's $\theta_t$ is a maximizer of $F_t$ (hence that unique one);
--   3. $\theta_t=\sum_{i=1}^{d}p_{t,i}\,c_{t-1,i}$, where $p_t$ are the algorithm's weights;
--   4. the play $x_t$, $x_{t,i}=p_{t,i}\big(1-(c_{t-1,i}-\theta_t)/2\big)$, lies in the probability simplex $\Delta_d$.
--
--   This shows that each step of the algorithm is well defined and that it plays a probability vector.
--
--   Differences from the source:
--   - reading: Algorithm 1 with β = 1/32 and "Assume β < 1/2" → the algorithm parametrized by β; reason: the lemma varies β, which Algorithm 1 fixes; the proof of Theorem 1 (p.8) says "The choices η = 1/8 and β = 1/32 in Algorithm 1 satisfy the conditions in Lemma 1"
--   - correction: β < 1/2 → 0 < β < 1/2; reason: for β = 0 and any d ≥ 1, F_t is constant in θ, every θ is a maximizer and θ_t is not unique; for β < 0, F_t(θ) → +∞ as |θ| → ∞ and no maximizer exists
--   - generalization: Algorithm 1's η = 1/8; c_s ∈ [−1,1]^d on every round s → any real η; only c_{t−1} ∈ [−1,1]^d is assumed; reason: the proof (p.7) uses only c_{t−1} ∈ [−1,1]^d (for Var ≤ 1 and for x_t ≥ 0), and −ηL_{t−1} enters as an arbitrary shift of the weights, so neither the value of η nor the earlier losses matter; the statement specializes to η = 1/8 with every c_s ∈ [−1,1]^d
--   - encoding: Δ_d for an unspecified d → d ≥ 1; reason: Δ_0 is empty, so the model and x_t ∈ Δ_d need d ≥ 1; only an undefined case is excluded
--   - encoding: [d], c_0 = 0 → Fin d, losses read through lossAt; reason: Lean convention; same instances
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Lemma 1, p.6 (proof p.7)

import Mathlib
import Definitions.Def_AltRegret_play

namespace AltRegret

/-- **Lemma 1 (well-posedness and feasibility of Algorithm 1).** Tao–Zheng, *Optimal Alternating
Regret for Online Learning and Games*, arXiv:2608.24731, Lemma 1, p.6: "Assume `β < 1/2`. In
Algorithm 1, `θ_t` is unique and `θ_t = ∑_{i=1}^d p_{t,i} c_{t−1,i}`. Moreover, `x_t ∈ Δ_d`."

For `d ≥ 1`, `0 < β < 1/2`, any `η`, any round `t ≥ 1` and any losses with
`c_{t−1} ∈ [−1,1]^d`: the objective `F_t(θ) = log ∑_i exp(−ηL_{t−1,i} − β(c_{t−1,i} − θ)²)` of
line 3 has exactly one maximizer; the algorithm's `θ_t` is a maximizer (hence that one);
`θ_t = ∑_i p_{t,i} c_{t−1,i}`; and the play `x_t` lies in the simplex `Δ_d`.

**Formalization Note.** `Fin d` indexes `[d]` (Lean index `i` is the paper's `i + 1`); `d ≥ 1` is
the paper's standing assumption that `Δ_d` is nonempty. The algorithm is parametrized by
`(η, β)` (Algorithm 1 is `η = 1/8`, `β = 1/32`). The hypothesis `0 < β` corrects the printed
`β < 1/2`: for `β = 0`, `F_t` is constant and every `θ` maximizes it. Only the loss read by round
`t`'s θ-step, `c_{t−1}`, is assumed bounded (`c₀ = 0` by `lossAt`). -/
theorem lemma_1 {d : ℕ} (hd : 0 < d) (η β : ℝ) (hβ0 : 0 < β) (hβ : β < 1 / 2)
    (c : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hc : ∀ i, lossAt c (t - 1) i ∈ Set.Icc (-1 : ℝ) 1) :
    (∃! θ : ℝ, ∀ θ' : ℝ, thetaObjective η β c t θ' ≤ thetaObjective η β c t θ) ∧
    (∀ θ' : ℝ, thetaObjective η β c t θ' ≤ thetaObjective η β c t (theta η β c t)) ∧
    theta η β c t = ∑ i, weights η β c t i * lossAt c (t - 1) i ∧
    play η β c t ∈ stdSimplex ℝ (Fin d) := by sorry

end AltRegret
