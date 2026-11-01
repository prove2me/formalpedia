-- Prove2me | Theorems.Thm_ExpConMinimax_lemma_21_a
-- name    : ExpConMinimax.lemma_21_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:36.455079+00:00
-- url     : https://prove2.me/theorems/8f373498-20c1-4fbd-a8ad-6c7b98b62d52
-- title:
--   Lemma 21(a) (corrected: $\mathbb E\|\pi\|$ replaced by $(\mathbb E\|\pi\|^2)^{1/2}$) — martingale-difference sum bound
-- statement:
--   Let $\delta_0,\dots,\delta_{N-1}$ be random vectors in $\mathbb R^m$ such that $\mathbb E[\delta_t\mid\delta_0,\dots,\delta_{t-1}]=0$ for $1\le t\le N-1$ and
--   $$\mathbb E\big[\|\delta_t\|^2\,\big|\,\delta_0,\dots,\delta_{t-1}\big]\le\sigma^2\qquad(0\le t\le N-1),$$
--   with $\sigma\ge0$. Then for every random vector $\pi$ with $\mathbb E\|\pi\|^2<\infty$ (possibly dependent on all the $\delta_t$),
--   $$\mathbb E\Big[\sum_{t=0}^{N-1}\pi^\top\delta_t\Big]\ \le\ \sqrt N\,\big(\mathbb E\|\pi\|^2\big)^{1/2}\,\sigma .$$
--
--   The paper prints $\sqrt N\,\mathbb E[\|\pi\|]\,\sigma$ on the right, which is false: with $N=1$, a scalar $\delta_0$ equal to $2$ with probability $1/3$ and to $-1$ with probability $2/3$ (so $\mathbb E\delta_0^2=2=\sigma^2$), and $\pi=\mathbf 1\{\delta_0=2\}$, one has $\mathbb E[\pi\delta_0]=2/3>\sqrt2/3=\sqrt N\,\mathbb E|\pi|\,\sigma$.
--
--   The lemma controls the noise term $\sum_t(H(x_t)-h(x_t,\xi^1_t))^\top\gamma$ against a random reference multiplier $\gamma$ in Lemma 5.
--
--   Differences from the source:
--   - correction: $\sqrt N\,\mathbb E[\|\pi\|]\,\sigma$ → $\sqrt N\,(\mathbb E\|\pi\|^2)^{1/2}\,\sigma$; reason: the printed bound is false: $N=1$, $\delta_0\in\{2,-1\}$ with probabilities $1/3,2/3$, $\sigma^2=2$, $\pi=\mathbf 1\{\delta_0=2\}$ gives $2/3>\sqrt2/3$
--   - encoding: random variables $\delta_t$, $\pi$ with $\pi^\top\delta_t$ → $\delta_t$, $\pi$ in a Euclidean space; conditioning on $\sigma(\delta_0,\dots,\delta_{t-1})$; reason: the paper's setting
--   - encoding: $\mathbb E[\|\delta_t\|^2\mid\cdot]\le\sigma^2$ → plus: each $\delta_t$ measurable and square integrable; reason: implied by the bound (it gives $\mathbb E\|\delta_t\|^2\le\sigma^2$); it makes the Lean conditional expectations meaningful
--   - reading: $\sigma^2$ bounds the conditional second moment → $\sigma\ge0$; reason: $\sigma$ is the nonnegative root; with $\sigma<0$ the right side is negative even for $\delta\equiv0$
--   - reading: $\mathbb E[\|\delta_t\|^2\mid\delta_0,\dots,\delta_{t-1}]\le\sigma^2$ (range of $t$ not printed) → for every $0\le t\le N-1$, the $\sigma$-algebra being trivial at $t=0$; reason: the bound is used for every term of the sum, and the bound on $\mathbb E\|\delta_0\|^2$ is needed already at $N=1$
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Lemma 21(a), p.27

import Mathlib
import Definitions.Def_ExpConMinimax_Vec
import Definitions.Def_ExpConMinimax_pastSigma

namespace ExpConMinimax

open MeasureTheory

/-- **Lemma 21(a)** (corrected: `E‖π‖` replaced by `(E‖π‖²)^{1/2}`).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Lemma 21(a), p.27:

"Let `{δₜ}_{t=0}^{N−1}` be a sequence of random variables. Suppose `δₜ` is conditionally
mean-zero such that `E[δₜ | δ₀,δ₁,⋯,δ_{t−1}] = 0` for all `t ≥ 1`. For any `π` such that
`E[‖π‖²] < +∞`, it holds that: (a) Suppose `E[‖δₜ‖² | δ₀,δ₁,⋯,δ_{t−1}] ≤ σ²`, then
`E[∑_{t=0}^{N−1} πᵀδₜ] ≤ √N E[‖π‖]σ`."

Stated here with `√N (E‖π‖²)^{1/2} σ` on the right. **The printed bound is false**: take
`N = 1`, a scalar `δ₀` equal to `2` with probability `1/3` and to `−1` with probability `2/3`
(so `E δ₀² = 2 = σ²`), and `π = 𝟙{δ₀ = 2}`; then `E[πδ₀] = 2/3 > √2/3 = √N E|π| σ`.

**Formalization Note.** `δₜ` and `π` take values in `ℝᵐ`; `π` is any square-integrable random
vector (it may depend on all the `δₜ`). The conditioning σ-algebra is
`pastSigma δ t = σ(δ₀,…,δ_{t−1})`. The conditional second-moment bound is required for every
`t < N`; at `t = 0` the σ-algebra is trivial and the bound reads `E‖δ₀‖² ≤ σ²`. The `δₜ` are measurable and square
integrable (the conditional second-moment bound implies `E‖δₜ‖² ≤ σ²`; square integrability
makes the Lean conditional expectations meaningful). `σ ≥ 0`. -/
theorem lemma_21_a {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {m : ℕ} (N : ℕ) (δ : ℕ → Ω → Vec m) (hδ_meas : ∀ t < N, Measurable (δ t))
    (hδ_L2 : ∀ t < N, MemLp (δ t) 2 Pr)
    (hδ_mean : ∀ t, 1 ≤ t → t < N → condExp (pastSigma δ t) Pr (δ t) =ᵐ[Pr] 0)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hδ_var : ∀ t < N,
      condExp (pastSigma δ t) Pr (fun ω => ‖δ t ω‖ ^ 2) ≤ᵐ[Pr] fun _ => σ ^ 2)
    (π : Ω → Vec m) (hπ : MemLp π 2 Pr) :
    ∫ ω, ∑ t ∈ Finset.range N, inner ℝ (π ω) (δ t ω) ∂Pr ≤
      Real.sqrt N * Real.sqrt (∫ ω, ‖π ω‖ ^ 2 ∂Pr) * σ := by sorry

end ExpConMinimax
