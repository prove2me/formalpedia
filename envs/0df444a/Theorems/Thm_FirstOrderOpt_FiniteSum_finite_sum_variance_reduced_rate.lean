-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_finite_sum_variance_reduced_rate
-- name    : FirstOrderOpt.FiniteSum.finite_sum_variance_reduced_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:02:20.644983+00:00
-- url     : https://prove2.me/theorems/f7d473d8-2e11-4151-984e-966d1ed96276
-- title:
--   Corollary 5.8 (goal theorem) — explicit-constant complexity bound for variance-reduced mirror descent
-- statement:
--   Variance-reduced mirror descent (Algorithm 5.6) solves the finite-sum composite problem
--   $\min_{x\in X}\{\Psi(x):=f(x)+h(x)\}$, $f=\frac1m\sum_{i=1}^m f_i$, with each $\nabla f_i$
--   $L_i$-Lipschitz, using an epoch structure with epoch-$s$ snapshot average $\tilde x_s$ and
--   overall weighted average $\bar x_S=\big(\sum_{s=1}^S w_s\tilde x_s\big)/\sum_{s=1}^S w_s$
--   (Theorem 5.6).
--
--   **Corollary 5.8.** Suppose $\theta=1$, $\gamma=1/(16L_Q)$, and the epoch lengths double,
--   $T_s=2T_{s-1}$ for $s=2,3,\dots$, with $T_1=7$ (Eq. (5.3.17)). Then for any $S\ge1$,
--   $$\mathbb E[\Psi(\bar x_S)-\Psi(x^*)] \le \frac{8}{2^{S-1}}\left[\frac{11}{4}\big(\Psi(x_0)-\Psi(x^*)\big)+16L_Q\,V(x_0,x^*)\right].$$
--
--   This is the chapter's headline result: an explicit-constant, exponentially decaying complexity
--   bound for variance-reduced mirror descent on smooth finite-sum problems without strong
--   convexity, instantiating Theorem 5.6's general epoch-weight bound with a concrete stepsize and
--   a doubling epoch schedule. Lan shows (not formalized here — see *Formalization scope*) this
--   translates to $O\big(m\log(\cdot)+(\cdot)/\varepsilon\big)$ total gradient computations to
--   reach an $\varepsilon$-solution, improving the plain mirror-descent method's $O(m/\varepsilon)$
--   dependence on the number of components $m$.
--
--   **Formalization Note.** $\bar x_S$ is defined via the same weighted-average apparatus as
--   Theorem 5.6 ($w$, the epoch snapshots $\tilde x_s$), rather than assumed abstractly, so this
--   goal is self-contained without literally taking Theorem 5.6 as a hypothesis — matching this
--   series' convention for a corollary stated as the mission's goal. $S-1$ in $2^{S-1}$ is
--   well-defined since $S\ge1$.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 281, Corollary 5.8

import Mathlib

namespace FirstOrderOpt.FiniteSum

open MeasureTheory

/-- Corollary 5.8 (goal theorem) — explicit-constant complexity bound for variance-reduced mirror
descent on smooth finite-sum problems without strong convexity. Instantiating Theorem 5.6's
epoch-weight schedule with `θ = 1`, `γ = 1/(16LQ)`, and the doubling schedule `T1 = 7`,
`Ts = 2T_{s-1}` (5.3.17), the epoch average `x̄S` (as in Theorem 5.6, (5.3.16)) satisfies
`E[Ψ(x̄S)-Ψ(x*)] ≤ (8/2^{S-1})·[(11/4)(Ψ(x0)-Ψ(x*)) + 16LQ·V(x0,x*)]` (5.3.18) for every `S ≥ 1`.

**Formalization Note (revised 2026-09-19).** `x̄S` is defined via the same weighted-average
apparatus as Theorem 5.6 (`w`, `xtilde`), rather than assumed abstractly, so the goal is
self-contained without literally importing Theorem 5.6 as a hypothesis (matching this series'
convention for a corollary-as-goal). `w`'s defining formula is extended to `s ≥ 1` using
`T 0 := T 1 / 2 = 3.5` (`hT0`), the same convention `epoch_convergence_bound` generalizes;
concretely this pins `w 1 = (3/4)(3.5-1) - (1/4)·7 = 1/8`, reproducing Corollary 5.8's own
arithmetic. `hepoch` (mirroring `epoch_convergence_bound`) restores the connection between
`xtilde s` and the algorithm's actual per-epoch dynamics via an auxiliary epoch-boundary sequence
`x` (`x 0 := x0`, `xtilde 0 := x0`) — without it, `xtilde s` is merely constrained to `X`, and an
arbitrarily-`Ψ`-large, `ω`-independent `xtilde 1` makes the stated bound false regardless of `w`.
`hintx`/`hintxtilde`/`hintVxs` guard the new integrals per Trap 2, as in `epoch_convergence_bound`.
`S - 1` is natural-number subtraction, matching `(2:ℝ)^(S-1)` in (5.3.18) (well-defined since
`S ≥ 1`). -/
theorem finite_sum_variance_reduced_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (Ψ : E → ℝ) (V : E → E → ℝ)
    (LQ : ℝ) (hLQ : 0 < LQ)
    (γ : ℝ) (hγ : γ = 1 / (16 * LQ))
    (T : ℕ → ℝ) (hT1 : T 1 = 7) (hT0 : T 0 = T 1 / 2) (hTrec : ∀ s, 2 ≤ s → T s = 2 * T (s - 1))
    (w : ℕ → ℝ) (hw : ∀ s, 1 ≤ s → w s = (1 - 4 * LQ * γ) * (T (s - 1) - 1) - 4 * LQ * γ * T s)
    (hwpos : ∀ s, 1 ≤ s → 0 < w s)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (S : ℕ) (hS : 1 ≤ S)
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
      (8 / (2 : ℝ) ^ (S - 1)) * ((11 / 4) * (Ψ x0 - Ψ xstar) + 16 * LQ * V x0 xstar) := by sorry

end FirstOrderOpt.FiniteSum
