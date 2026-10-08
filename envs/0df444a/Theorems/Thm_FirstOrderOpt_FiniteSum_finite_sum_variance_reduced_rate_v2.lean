-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_finite_sum_variance_reduced_rate_v2
-- name    : FirstOrderOpt.FiniteSum.finite_sum_variance_reduced_rate_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:06.6614+00:00
-- url     : https://prove2.me/theorems/d655a74e-5a8c-4668-afd4-3a34b9d2211c
-- title:
--   Corollary 5.8 — explicit rate of variance-reduced mirror descent (corrected: Bregman $V$)
-- statement:
--   Let $X$ be closed convex, $\nu$ a distance generating function on $X$ with prox-function $V$, and $\Psi$ convex on $X$ with optimal solution $x^*$. Instantiate Theorem 5.6 with $\theta_t=1$, $\gamma=1/(16L_Q)$, $T_1=7$, $T_s=2T_{s-1}$ (5.3.17) and the weights $w_s$ of (5.3.14) (with the convention $T_0=T_1/2$ for $w_1$), with the epoch-boundary iterates $x_s$ and snapshots $\tilde x_s$ satisfying the per-epoch progress inequality of Theorem 5.6. Then for every $S\ge 1$ the epoch average $\bar x_S$ satisfies (5.3.18)
--   $$\mathbb E\big[\Psi(\bar x_S)\big]-\Psi(x^*)\le\frac8{2^{S-1}}\Big[\tfrac{11}4\big(\Psi(x_0)-\Psi(x^*)\big)+16L_Q\,V(x_0,x^*)\Big].$$
--
--   **Formalization Note.** The retired statement's free $V$ admitted $V\equiv-1$ (disproved). The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. Convexity of $\Psi$ and closed convexity of $X$ are stated. The per-epoch inequality `hepoch` (the display in the book's proof obtained by summing Lemma 5.14 over an epoch, with the epoch-boundary iterates $x_s$ and snapshots $\tilde x_s$, $x_0=\tilde x_0$) and the convention $T_0$ for the weight $w_1$ are kept from the retired statement: the exact printed form of Algorithm 5.6's epoch bookkeeping ((5.3.12), (5.3.14), (5.3.16)) could not be re-verified against the book in this revision, so the statement abstracts the algorithm by that inequality rather than restating the inner loop; this is recorded as a residual abstraction to be removed once the text is at hand.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 281, Corollary 5.8, with (5.3.17)-(5.3.18)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.FiniteSum

open MeasureTheory FirstOrderOpt.Prox

/-- Corollary 5.8, Lan p. 281 — explicit complexity bound for variance-reduced mirror descent on
smooth finite-sum problems without strong convexity. Let `X` be closed convex, `ν` a distance
generating function on `X` with prox-function `V = ν.V`, `Ψ` convex. Instantiating Theorem 5.6
with `θ = 1`, `γ = 1/(16LQ)` and the doubling schedule `T1 = 7`, `Ts = 2T_{s-1}` (5.3.17), the
epoch average `x̄S` of (5.3.16) satisfies, for every `S ≥ 1`,
`E[Ψ(x̄S) - Ψ(x*)] ≤ (8/2^{S-1})·[(11/4)(Ψ(x0) - Ψ(x*)) + 16LQ·V(x0, x*)]` (5.3.18).

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
free `V` admitted `V ≡ -1`), `Ψ` is convex and `X` closed convex. The epoch recursion `hepoch`
(Theorem 5.6's per-epoch inequality) and the `T 0 := T 1 / 2` convention for `w 1` are kept from
the retired statement (see the Formalization Note). -/
theorem finite_sum_variance_reduced_rate_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (Ψ : E → ℝ) (hΨconv : ConvexOn ℝ X Ψ)
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
    (hintVxs : ∀ s, Integrable (fun ω => ν.V (x s ω) xstar) μ)
    (hepoch : ∀ s, 1 ≤ s →
      γ * (∫ ω, Ψ (x s ω) ∂μ - Ψ xstar) +
        (1 - 4 * LQ * γ) * γ * (T s - 1) * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) +
        ∫ ω, ν.V (x s ω) xstar ∂μ
      ≤ γ * (∫ ω, Ψ (x (s - 1) ω) ∂μ - Ψ xstar) +
        4 * LQ * γ ^ 2 * T s * (∫ ω, Ψ (xtilde (s - 1) ω) ∂μ - Ψ xstar) +
        ∫ ω, ν.V (x (s - 1) ω) xstar ∂μ)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω =
      (∑ s ∈ Finset.Icc 1 S, w s)⁻¹ • ∑ s ∈ Finset.Icc 1 S, w s • xtilde s ω)
    (hint : Integrable (fun ω => Ψ (xbar ω)) μ) :
    ∫ ω, Ψ (xbar ω) ∂μ - Ψ xstar ≤
      (8 / (2 : ℝ) ^ (S - 1)) * ((11 / 4) * (Ψ x0 - Ψ xstar) + 16 * LQ * ν.V x0 xstar) := by sorry

end FirstOrderOpt.FiniteSum
