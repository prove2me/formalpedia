-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_epoch_convergence_bound_v2
-- name    : FirstOrderOpt.FiniteSum.epoch_convergence_bound_v2
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:16:56.474606+00:00
-- url     : https://prove2.me/theorems/e82645f2-9b9b-499d-a738-1e9d424fa540
-- title:
--   Theorem 5.6 — variance-reduced mirror descent, general epoch bound (5.3.15) (corrected: Bregman $V$)
-- statement:
--   Let $X$ be closed convex, $\nu$ a distance generating function on $X$ with prox-function $V$, and $\Psi$ convex on $X$ with optimal solution $x^*$. Run Algorithm 5.6 (variance-reduced mirror descent) with $\theta_t=1$ (5.3.12), stepsize $\gamma$ with $4L_Q\gamma\le 1$ (5.3.13), epoch lengths $T_s\ge 1$ and epoch weights $w_s=(1-4L_Q\gamma)(T_{s-1}-1)-4L_Q\gamma T_s$ (5.3.14), assumed positive. Let $x_s$ be the iterate at the end of epoch $s$ ($x_0$ the starting point) and $\tilde x_s$ the epoch snapshot ($\tilde x_0=x_0$), satisfying for every epoch $s\ge 1$ the progress inequality
--   $$\gamma\big(\mathbb E\Psi(x_s)-\Psi^*\big)+(1-4L_Q\gamma)\gamma(T_s-1)\big(\mathbb E\Psi(\tilde x_s)-\Psi^*\big)+\mathbb E V(x_s,x^*)\le\gamma\big(\mathbb E\Psi(x_{s-1})-\Psi^*\big)+4L_Q\gamma^2T_s\big(\mathbb E\Psi(\tilde x_{s-1})-\Psi^*\big)+\mathbb E V(x_{s-1},x^*)$$
--   (Lemma 5.14 summed over the epoch). Then the weighted average $\bar x_S=\sum_{s=1}^Sw_s\tilde x_s/\sum_{s=1}^Sw_s$ (5.3.16) satisfies (5.3.15)
--   $$\mathbb E\big[\Psi(\bar x_S)\big]-\Psi(x^*)\le\frac{\gamma(1+4L_Q\gamma T_1)\big[\Psi(x_0)-\Psi(x^*)\big]+V(x_0,x^*)}{\gamma\sum_{s=1}^Sw_s}.$$
--
--   **Formalization Note.** The retired statement's free $V$ admitted $V\equiv-1$, which satisfies every hypothesis while the right-hand side becomes negative (disproved). The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. Convexity of $\Psi$ (Jensen at $\bar x_S$) and closed convexity of $X$ are stated. The per-epoch inequality `hepoch` (the display in the book's proof obtained by summing Lemma 5.14 over an epoch, with the epoch-boundary iterates $x_s$ and snapshots $\tilde x_s$, $x_0=\tilde x_0$) and the convention $T_0$ for the weight $w_1$ are kept from the retired statement: the exact printed form of Algorithm 5.6's epoch bookkeeping ((5.3.12), (5.3.14), (5.3.16)) could not be re-verified against the book in this revision, so the statement abstracts the algorithm by that inequality rather than restating the inner loop; this is recorded as a residual abstraction to be removed once the text is at hand.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 280, Theorem 5.6, with (5.3.12)-(5.3.16)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.FiniteSum

open MeasureTheory FirstOrderOpt.Prox

/-- Theorem 5.6 (general variance-reduced mirror descent convergence bound), Lan p. 280. Let
`X` be closed convex, `ν` a distance generating function on `X` with prox-function `V = ν.V`,
`Ψ = f + h` convex with `h` convex (the finite-sum setting of §5.3 with constant `LQ`), and run
Algorithm 5.6 with `θt = 1` (5.3.12), `4LQγ ≤ 1` (5.3.13) and the epoch-weight definition
`ws := (1-4LQγ)(T_{s-1}-1) - 4LQγTs` (5.3.14), assumed positive. With `x s` the iterate at the
end of epoch `s` (`x 0 = x0`), `x̃ s` the epoch snapshot (`x̃ 0 = x0`) and the per-epoch progress
inequality that Lemma 5.14 summed over epoch `s` yields (`hepoch`, the display on p. 281 of the
proof), the weighted average `x̄S := (Σ_{s=1}^S ws·x̃s)/Σ_{s=1}^S ws` (5.3.16) satisfies
`E[Ψ(x̄S) - Ψ(x*)] ≤ (γ(1+4LQγT1)[Ψ(x0)-Ψ(x*)] + V(x0,x*)) / (γ Σ_{s=1}^S ws)` (5.3.15).

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
free `V` admitted `V ≡ -1`, making the right-hand side negative), `Ψ` is convex and `X` closed
convex (standing assumptions). The epoch recursion `hepoch` and the `T 0` convention for `w 1`
are kept from the retired statement (see the Formalization Note). -/
theorem epoch_convergence_bound_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (Ψ : E → ℝ) (hΨconv : ConvexOn ℝ X Ψ)
    (LQ γ : ℝ) (hLQ : 0 < LQ) (hγ : 0 < γ) (h4LQγ : 4 * LQ * γ ≤ 1)
    (T : ℕ → ℝ) (hT0pos : 0 < T 0) (hTpos : ∀ s, 1 ≤ s → 1 ≤ T s)
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
      (γ * (1 + 4 * LQ * γ * T 1) * (Ψ x0 - Ψ xstar) + ν.V x0 xstar) /
        (γ * ∑ s ∈ Finset.Icc 1 S, w s) := by sorry

end FirstOrderOpt.FiniteSum
