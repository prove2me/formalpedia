-- Prove2me | Theorems.Thm_ExpConMinimax_lemma_21_b
-- name    : ExpConMinimax.lemma_21_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:45.037145+00:00
-- url     : https://prove2.me/theorems/9c0ed373-5193-4778-8ced-2003720cbe84
-- title:
--   Lemma 21(b) — $\mathbb E\sum_t\pi^\top\delta_t\le\frac\tau2\mathbb E\|\pi\|^2+\sum_t\frac1{2\tau}\mathbb E\|\delta_t\|^2$
-- statement:
--   Let $\delta_0,\dots,\delta_{N-1}$ be random vectors in $\mathbb R^m$ with $\mathbb E[\delta_t\mid\delta_0,\dots,\delta_{t-1}]=0$ for $1\le t\le N-1$, let $\pi$ be a random vector with $\mathbb E\|\pi\|^2<\infty$, and let $\tau>0$. Then
--   $$\mathbb E\Big[\sum_{t=0}^{N-1}\pi^\top\delta_t\Big]\ \le\ \frac\tau2\,\mathbb E\|\pi\|^2+\sum_{t=0}^{N-1}\frac1{2\tau}\,\mathbb E\|\delta_t\|^2 .$$
--
--   Used in Lemma 5 for the term $\sum_t(\widetilde\nabla_xL-\widetilde\nabla_x\mathcal L)^\top x$ with a random reference point $x$.
--
--   Differences from the source:
--   - encoding: random variables $\delta_t$, $\pi$ with $\pi^\top\delta_t$ → $\delta_t$, $\pi$ in a Euclidean space; conditioning on $\sigma(\delta_0,\dots,\delta_{t-1})$; reason: the paper's setting
--   - encoding: no integrability stated for $\delta_t$ → each $\delta_t$ measurable and square integrable; reason: if some $\mathbb E\|\delta_t\|^2=+\infty$ the printed bound is trivially true, while a Lean integral of a non-integrable function is $0$
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Lemma 21(b), p.27

import Mathlib
import Definitions.Def_ExpConMinimax_Vec
import Definitions.Def_ExpConMinimax_pastSigma

namespace ExpConMinimax

open MeasureTheory

/-- **Lemma 21(b)** (Young-type bound for a martingale-difference sum).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Lemma 21(b), p.27:

"Let `{δₜ}_{t=0}^{N−1}` be a sequence of random variables. Suppose `δₜ` is conditionally
mean-zero such that `E[δₜ | δ₀,δ₁,⋯,δ_{t−1}] = 0` for all `t ≥ 1`. For any `π` such that
`E[‖π‖²] < +∞`, it holds that: … (b) Let `τ > 0` be a positive number, then
`E[∑_{t=0}^{N−1} πᵀδₜ] ≤ τ/2 E[‖π‖²] + ∑_{t=0}^{N−1} 1/(2τ) E[‖δₜ‖²]`."

**Formalization Note.** `δₜ` and `π` take values in `ℝᵐ`; `π` is any square-integrable random
vector. The conditioning σ-algebra is `pastSigma δ t = σ(δ₀,…,δ_{t−1})`. The `δₜ` are
measurable and square integrable: when some `E‖δₜ‖² = +∞` the printed bound is trivially
true, while the Lean Bochner integral of a non-integrable function is `0`. -/
theorem lemma_21_b {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {m : ℕ} (N : ℕ) (δ : ℕ → Ω → Vec m) (hδ_meas : ∀ t < N, Measurable (δ t))
    (hδ_L2 : ∀ t < N, MemLp (δ t) 2 Pr)
    (hδ_mean : ∀ t, 1 ≤ t → t < N → condExp (pastSigma δ t) Pr (δ t) =ᵐ[Pr] 0)
    (π : Ω → Vec m) (hπ : MemLp π 2 Pr) (τ : ℝ) (hτ : 0 < τ) :
    ∫ ω, ∑ t ∈ Finset.range N, inner ℝ (π ω) (δ t ω) ∂Pr ≤
      τ / 2 * ∫ ω, ‖π ω‖ ^ 2 ∂Pr
        + ∑ t ∈ Finset.range N, 1 / (2 * τ) * ∫ ω, ‖δ t ω‖ ^ 2 ∂Pr := by sorry

end ExpConMinimax
