-- Prove2me | Theorems.Thm_AltRegret_lemma_2
-- name    : AltRegret.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:36.987353+00:00
-- url     : https://prove2.me/theorems/2088cb35-180f-4f48-949a-a562a4c3cd56
-- title:
--   Lemma 2 — the one-step inequality $\log\sum_i p_{t,i}\exp(\cdots)\le0$, vector form (corrected: $\eta\ge0$)
-- statement:
--   Let $0\le\eta\le1/8$ and $\beta=\eta/4$. Let $p\in\Delta_d$, let $\xi\in[-2,2]^d$ with $\sum_{i=1}^d p_i\xi_i=0$, let $x\in\mathbb R^d$ be given by $x_i=p_i(1-\xi_i/2)$, and let $z\in[-2,2]^d$. Then
--   $$
--   \log\sum_{i=1}^{d}p_i\exp\!\Big(\eta\big((\xi+z)^\top x-\xi_i-z_i\big)+\beta\big(\xi_i^2-z_i^2\big)\Big)\le0 .
--   $$
--   In the paper, $p=p_t$, $\xi=\xi_t=c_{t-1}-\theta_t\mathbf 1$, $x=x_t$ and $z=\xi_{t+1}=c_t-\theta_{t+1}\mathbf 1$, and the left side is $\Phi_{t+1}-\Phi_t$. The inequality is the one-step decrease of the potential (Theorem 5).
--
--   Differences from the source:
--   - generalization: p_t, ξ_t, ξ_{t+1}, x_t of the algorithm at rounds t and t+1 → arbitrary p ∈ Δ_d, ξ ∈ [−2,2]^d with pᵀξ = 0, x with x_i = p_i(1 − ξ_i/2), z ∈ [−2,2]^d; reason: the proof of Theorem 5 (p.7) derives exactly these properties from Lemma 1 at rounds t and t+1 ("ξt, ξt+1 ∈ [−2, 2]d, p⊤t ξt = 0, and the update gives xt,i = pt,i(1 − ξt,i/2)"), and the proof of Lemma 2 works on the whole box [−2,2]^d, so the statement specializes to the printed one for η > 0; at η = 0 (β = 0) Lemma 1 does not apply, and the printed left side is log Σ_i p_{t,i} = 0 outright
--   - correction: η ≤ 1/8 → 0 ≤ η ≤ 1/8; reason: for η < 0 the inequality is false. d = 1, p = (1), ξ = (0), x = (1), z = (2), η = −1/8, β = −1/32 satisfy every other hypothesis and the left side is −4β = 1/8 > 0 (at the algorithm level η < 0 makes θ_t undefined)
--   - encoding: [d] → Fin d; reason: Lean convention; same instances
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Lemma 2, p.8 (setting from the proof of Theorem 5, p.7)

import Mathlib

namespace AltRegret

/-- **Lemma 2 (one-step inequality), vector form.** Tao–Zheng, arXiv:2608.24731, Lemma 2, p.8:
"Assume `η ≤ 1/8` and `β = η/4`. Then for any `t ≥ 1`, we have
`log(∑_{i=1}^d p_{t,i} exp(η((ξ_t + ξ_{t+1})ᵀx_t − ξ_{t,i} − ξ_{t+1,i}) + β(ξ²_{t,i} − ξ²_{t+1,i}))) ≤ 0`."

Let `0 ≤ η ≤ 1/8` and `β = η/4`. Let `p ∈ Δ_d`, `ξ ∈ [−2,2]^d` with `∑_i p_i ξ_i = 0`, let
`x_i = p_i(1 − ξ_i/2)`, and let `z ∈ [−2,2]^d`. Then
`log ∑_i p_i exp(η((ξ + z)ᵀx − ξ_i − z_i) + β(ξ_i² − z_i²)) ≤ 0`.

**Formalization Note.** The proof of Theorem 5 (p.7) obtains exactly these properties for
`p = p_t`, `ξ = ξ_t = c_{t−1} − θ_t𝟏`, `x = x_t`, `z = ξ_{t+1} = c_t − θ_{t+1}𝟏` from Lemma 1 at
rounds `t` and `t + 1`, so this statement specializes to the printed one. `0 ≤ η` corrects the
printed `η ≤ 1/8`: with `d = 1`, `p = (1)`, `ξ = 0`, `z = (2)`, `η = −1/8` the left side is `1/8`.
`Fin d` indexes `[d]`; `Real.log` is the natural logarithm. -/
theorem lemma_2 (η β : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hβ : β = η / 4) {d : ℕ}
    (p ξ x z : Fin d → ℝ) (hp : p ∈ stdSimplex ℝ (Fin d))
    (hξ : ∀ i, ξ i ∈ Set.Icc (-2 : ℝ) 2) (hpξ : ∑ i, p i * ξ i = 0)
    (hx : ∀ i, x i = p i * (1 - ξ i / 2)) (hz : ∀ i, z i ∈ Set.Icc (-2 : ℝ) 2) :
    Real.log (∑ i, p i * Real.exp
      (η * (∑ j, (ξ j + z j) * x j - ξ i - z i) + β * (ξ i ^ 2 - z i ^ 2))) ≤ 0 := by sorry

end AltRegret
