-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_epoch_convergence_bound
-- name    : FirstOrderOpt.FiniteSum.epoch_convergence_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:01:59.587059+00:00
-- url     : https://prove2.me/theorems/3f4f8ef5-2fd1-4c10-8b95-fe1eb2db9f8b
-- title:
--   Theorem 5.6 — general variance-reduced mirror descent convergence bound
-- statement:
--   Variance-reduced mirror descent (Algorithm 5.6) is a multi-epoch method: epoch $s$ runs
--   $T_s$ inner iterations starting from snapshot $\tilde x_{s-1}$ and outputs a new snapshot
--   $\tilde x_s:=\sum_{t=2}^{T_s}(\theta_t x_t)/\sum_{t=2}^{T_s}\theta_t$. Suppose $f$ is not
--   necessarily strongly convex ($\mu=0$), and the algorithmic parameters satisfy
--   $$\theta_t=1,\ t\ge1\ \ (5.3.12),\qquad 4L_Q\gamma\le1\ \ (5.3.13),\qquad
--   w_s:=(1-4L_Q\gamma)(T_{s-1}-1)-4L_Q\gamma T_s>0,\ s\ge2\ \ (5.3.14).$$
--
--   **Theorem 5.6.** For every $S\ge1$,
--   $$\mathbb E[\Psi(\bar x_S)-\Psi(x^*)] \le \frac{\gamma(1+4L_Q\gamma T_1)[\Psi(x_0)-\Psi(x^*)]+V(x_0,x^*)}{\gamma\sum_{s=1}^S w_s},$$
--   where $\bar x_S=\big(\sum_{s=1}^S w_s\tilde x_s\big)\big/\sum_{s=1}^S w_s$.
--
--   This is the chapter's general convergence result for variance-reduced mirror descent on smooth
--   finite-sum problems without strong convexity, obtained by summing Lemma 5.14's one-step
--   progress bound (with $\mu=0$) over each epoch's iterations, telescoping across epochs, and
--   using the convexity of $\Psi$. Corollary 5.8 specializes it to an explicit stepsize and epoch
--   schedule.
--
--   **Formalization Note.** As in the book, (5.3.14) pins down $w_s$ only for $s\ge2$; the
--   displayed sums in the conclusion run from $s=1$, so $w_1$ is left a free real number
--   satisfying only the standing positivity of every $w_s$ — this is a gap in the book's own text
--   (not one this formalization resolves by invention; see `STATUS.md`). The epoch snapshots
--   $\tilde x_s$ are modeled as random variables `E → Ω → E` over a probability space, produced by
--   Algorithm 5.6's random component sampling; $x_0$ and $x^*$ are deterministic. $T$ is
--   real-valued here since the epoch-length schedule is only fixed to an explicit doubling rule by
--   Corollary 5.8.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 280, Theorem 5.6

import Mathlib

namespace FirstOrderOpt.FiniteSum

open MeasureTheory

/-- Theorem 5.6 (general variance-reduced mirror descent convergence bound). Under `θt = 1`
(5.3.12), `4LQγ ≤ 1` (5.3.13), and the epoch-weight definition `ws := (1-4LQγ)(T_{s-1}-1) -
4LQγTs` for `s ≥ 2` (5.3.14, positive by hypothesis), the weighted average `x̄S := (Σ_{s=1}^S
ws·x̃s)/Σ_{s=1}^S ws` (5.3.16) of the epoch snapshots `x̃s` satisfies
`E[Ψ(x̄S)-Ψ(x*)] ≤ (γ(1+4LQγT1)[Ψ(x0)-Ψ(x*)]+V(x0,x*)) / (γΣ_{s=1}^S ws)` (5.3.15).

**Formalization Note (revised 2026-09-19).** `hw`'s domain is extended from the book's literal
`s ≥ 2` to `s ≥ 1`, using `T 0` (a fixed real, via `hT0pos`) as the "`s=0`" epoch length so `w 1`
is pinned by the same formula rather than left free — this is the same `T0` convention the goal
theorem `finite_sum_variance_reduced_rate` instantiates concretely (`T 0 = T 1 / 2`), generalized
here. More substantively: `xtilde s`, the epoch snapshot, is not an arbitrary point of `X` — it is
the output of running the variance-reduced mirror-descent update for `T s` iterations from
`xtilde (s-1)` (Algorithm 5.6). `hepoch` restores this connection via the per-epoch inequality the
book's own proof derives (PDF 294, from `variance_reduced_progress_bound`/Lemma 5.14 summed over an
epoch), using an auxiliary epoch-boundary sequence `x : ℕ → Ω → E` (`x 0 := x0`, `xtilde 0 := x0`,
matching the book's `x̃0 = x0`). Without `hepoch`, `xtilde s`'s only constraint is membership in
`X`, and a fixed-across-`ω`, arbitrarily-`Ψ`-large `xtilde 1 := z` makes the stated conclusion
false (`w1 → ∞` was one route; `hepoch` alone already blocks the unbounded-`Ψ(z)` construction,
since (with `T s ≥ 1` fixed) the left side of `hepoch` at `s=1` would then be unbounded while the
right side stays pinned to the finite `x0` data). `hintx`/`hintxtilde`/`hintVxs` guard `hepoch`'s
Bochner integrals with `Integrable`, per the same Trap-2 convention chunk `04-stochastic` was
fixed for — without these, a non-integrable `Ψ(x s ·)`/`Ψ(xtilde s ·)`/`V(x s ·) xstar` would make
`hepoch` vacuously true (`integral_undef`) regardless of the epoch's true progress. `x0` and
`xstar` are deterministic (the fixed starting point and an optimal solution). `T : ℕ → ℝ` is
real-valued since `w`'s defining formula is purely arithmetic here (the specific integer doubling
schedule is introduced only by Corollary 5.8). -/
theorem epoch_convergence_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (Ψ : E → ℝ) (V : E → E → ℝ)
    (LQ γ : ℝ) (hLQ : 0 < LQ) (hγ : 0 < γ) (h4LQγ : 4 * LQ * γ ≤ 1)
    (T : ℕ → ℝ) (hT0pos : 0 < T 0) (hTpos : ∀ s, 1 ≤ s → 0 < T s)
    (w : ℕ → ℝ)
    (hw : ∀ s, 1 ≤ s → w s = (1 - 4 * LQ * γ) * (T (s - 1) - 1) - 4 * LQ * γ * T s)
    (hwpos : ∀ s, 1 ≤ s → 0 < w s)
    (S : ℕ) (hS : 1 ≤ S)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (xtilde : ℕ → Ω → E) (hxtilde : ∀ s, 1 ≤ s → ∀ ω, xtilde s ω ∈ X)
    (x : ℕ → Ω → E) (hx : ∀ s, ∀ ω, x s ω ∈ X)
    (hx0eq : ∀ ω, x 0 ω = x0) (hxtilde0eq : ∀ ω, xtilde 0 ω = x0)
    (hintx : ∀ s, Integrable (fun ω => Ψ (x s ω)) μ)
    (hintxtilde : ∀ s, Integrable (fun ω => Ψ (xtilde s ω)) μ)
    (hintVxs : ∀ s, Integrable (fun ω => V (x s ω) xstar) μ)
    (hepoch : ∀ s, 1 ≤ s →
      γ * (∫ ω, Ψ (x s ω) ∂μ - Ψ xstar) +
        (1 - 4 * LQ * γ) * γ * (T s - 1) * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) +
        ∫ ω, V (x s ω) xstar ∂μ
      ≤ γ * (∫ ω, Ψ (x (s - 1) ω) ∂μ - Ψ xstar) +
        4 * LQ * γ ^ 2 * T s * (∫ ω, Ψ (xtilde (s - 1) ω) ∂μ - Ψ xstar) +
        ∫ ω, V (x (s - 1) ω) xstar ∂μ)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω =
      (∑ s ∈ Finset.Icc 1 S, w s)⁻¹ • ∑ s ∈ Finset.Icc 1 S, w s • xtilde s ω)
    (hint : Integrable (fun ω => Ψ (xbar ω)) μ) :
    ∫ ω, Ψ (xbar ω) ∂μ - Ψ xstar ≤
      (γ * (1 + 4 * LQ * γ * T 1) * (Ψ x0 - Ψ xstar) + V x0 xstar) /
        (γ * ∑ s ∈ Finset.Icc 1 S, w s) := by sorry

end FirstOrderOpt.FiniteSum
