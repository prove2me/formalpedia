-- Prove2me | Theorems.Thm_ExpConMinimax_lemma_21_c
-- name    : ExpConMinimax.lemma_21_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:57.51135+00:00
-- url     : https://prove2.me/theorems/ecdaff3d-508c-4781-ac8e-0061ea3a2918
-- title:
--   Lemma 21(c) — bound with weights $\tau_t+\rho_t\ge\tau_{t+1}$
-- statement:
--   Let $\delta_0,\dots,\delta_{N-1}$ be random vectors in $\mathbb R^m$ with $\mathbb E[\delta_t\mid\delta_0,\dots,\delta_{t-1}]=0$ for $1\le t\le N-1$, let $\pi$ be a random vector with $\mathbb E\|\pi\|^2<\infty$, and let $(\tau_t)$, $(\rho_t)$ be positive sequences with $\tau_t+\rho_t\ge\tau_{t+1}$. Then
--   $$\mathbb E\Big[\sum_{t=0}^{N-1}\pi^\top\delta_t\Big]\ \le\ \Big(\frac{\tau_0}2+\sum_{t=0}^{N-1}\frac{\rho_t}2\Big)\mathbb E\|\pi\|^2+\sum_{t=0}^{N-1}\frac1{2\tau_t}\,\mathbb E\|\delta_t\|^2 .$$
--
--   This generalizes part (b) (take $\tau_t\equiv\tau$, and let $\rho_t\downarrow0$) and serves the adaptive step sizes of §4.
--
--   Differences from the source:
--   - encoding: random variables $\delta_t$, $\pi$ with $\pi^\top\delta_t$ → $\delta_t$, $\pi$ in a Euclidean space; conditioning on $\sigma(\delta_0,\dots,\delta_{t-1})$; reason: the paper's setting
--   - encoding: no integrability stated for $\delta_t$ → each $\delta_t$ measurable and square integrable; reason: if some $\mathbb E\|\delta_t\|^2=+\infty$ the printed bound is trivially true, while a Lean integral of a non-integrable function is $0$
--   - encoding: positive sequences $\{\tau_t\},\{\rho_t\}$ with $\tau_t+\rho_t\ge\tau_{t+1}$ (index range not printed) → sequences on $\mathbb N$, the conditions holding for every $t$; reason: the bound reads only $t\le N-1$, and a finite sequence extends by $\tau_{t+1}=\tau_t$, $\rho_t=1$
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Lemma 21(c), p.27

import Mathlib
import Definitions.Def_ExpConMinimax_Vec
import Definitions.Def_ExpConMinimax_pastSigma

namespace ExpConMinimax

open MeasureTheory

/-- **Lemma 21(c)** (bound with time-varying weights).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Lemma 21(c), p.27:

"Let `{δₜ}_{t=0}^{N−1}` be a sequence of random variables. Suppose `δₜ` is conditionally
mean-zero such that `E[δₜ | δ₀,δ₁,⋯,δ_{t−1}] = 0` for all `t ≥ 1`. For any `π` such that
`E[‖π‖²] < +∞`, it holds that: … (c) Let `{τₜ}, {ρₜ}` be two positive sequences such that
`τₜ + ρₜ ≥ τₜ₊₁`, then
`E[∑_{t=0}^{N−1} πᵀδₜ] ≤ (τ₀/2 + ∑_{t=0}^{N−1} ρₜ/2) E[‖π‖²] + ∑_{t=0}^{N−1} 1/(2τₜ) E[‖δₜ‖²]`."

**Formalization Note.** As in Lemma 21(b): values in `ℝᵐ`, `π` any square-integrable random
vector, conditioning on `pastSigma δ t = σ(δ₀,…,δ_{t−1})`, the `δₜ` measurable and square
integrable. The sequences `τ, ρ` are indexed by `ℕ`. -/
theorem lemma_21_c {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {m : ℕ} (N : ℕ) (δ : ℕ → Ω → Vec m) (hδ_meas : ∀ t < N, Measurable (δ t))
    (hδ_L2 : ∀ t < N, MemLp (δ t) 2 Pr)
    (hδ_mean : ∀ t, 1 ≤ t → t < N → condExp (pastSigma δ t) Pr (δ t) =ᵐ[Pr] 0)
    (π : Ω → Vec m) (hπ : MemLp π 2 Pr) (τ ρ : ℕ → ℝ) (hτ : ∀ t, 0 < τ t)
    (hρ : ∀ t, 0 < ρ t) (hτρ : ∀ t, τ (t + 1) ≤ τ t + ρ t) :
    ∫ ω, ∑ t ∈ Finset.range N, inner ℝ (π ω) (δ t ω) ∂Pr ≤
      (τ 0 / 2 + ∑ t ∈ Finset.range N, ρ t / 2) * ∫ ω, ‖π ω‖ ^ 2 ∂Pr
        + ∑ t ∈ Finset.range N, 1 / (2 * τ t) * ∫ ω, ‖δ t ω‖ ^ 2 ∂Pr := by sorry

end ExpConMinimax
