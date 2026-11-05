-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_theorem_4_9_4
-- name    : BauerleRiederMDP.Indifference.theorem_4_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:06.915734+00:00
-- url     : https://prove2.me/theorems/7937b7f0-a8e0-4d4b-bda0-1e8566e74587
-- title:
--   Theorem 4.9.4 — value functions, indifference prices and consistency in the multiperiod market
-- statement:
--   Consider the multiperiod financial market of Section 4.9 with a contingent claim $H=h(S_N,\hat S_N)\ge 0$.
--
--   **a)** The value functions of problem (4.38) are given by
--   $$
--   V^H_n(x,s,\hat s)=-e^{-\gamma x}d_n(s,\hat s),
--   $$
--   where $(d_n)$ satisfy the recursion
--   $$
--   d_N(s,\hat s)=e^{\gamma h(s,\hat s)},\qquad d_n(s,\hat s)=\inf_{a\in\mathbb R}\mathbb E\Bigl[e^{-\gamma a(\tilde R_{n+1}-1)}d_{n+1}\bigl(s\tilde R_{n+1},\hat s\hat R_{n+1}\bigr)\Bigr].
--   $$
--   In particular $V^0_n(x,s,\hat s)=-e^{-\gamma x}v^{N-n}$.
--
--   **b)** The indifference price of $H$ is the unique solution of its defining equation and is given by
--   $$
--   v_n(H,s,\hat s)=\frac1\gamma\log\Bigl(\frac{d_n(s,\hat s)}{v^{N-n}}\Bigr).
--   $$
--
--   **c)** The indifference prices satisfy the consistency condition
--   $$
--   v_n\bigl(v_{n+1}(H,s\tilde R_{n+1},\hat s\hat R_{n+1}),s,\hat s\bigr)=v_n(H,s,\hat s),\qquad n=0,1,\dots,N-1.
--   $$
--   Here the inner price is a contingent claim with maturity $n+1$, a function of the prices at time $n+1$, and the outer price is its indifference price at time $n$ in the market with that maturity.
--
--   No closed formula for the price exists in general. The theorem reduces multiperiod indifference pricing to a backward recursion and shows that the price can be computed period by period, with the price at time $n+1$ acting as the payoff of a one-period claim.
--
--   **Formalization Note** The value function is the one of the published Markov Decision Model framework, so it is an extended real, and part a) says that it is the stated real number.
--
--   Differences from the source:
--   - reading: (FM) prints only d̂ < û → hypothesis 0 ≤ d̂; reason: the multiperiod model puts the relative price changes in 𝒵 := ℝ₊ × ℝ₊ (p.138), so the prices stay in ℝ₊ where the claim is non-negative
--   - reading: v_n is the value which satisfies the defining equation, and b) gives its formula → a number solves the defining equation if and only if it is the formula, and the price function equals the formula; reason: the book presupposes existence and uniqueness; this states them
--   - reading: c) holds on Ω, with the inner price a random variable → the inner price is a claim W with maturity n + 1, measurable, non-negative and equal to v_{n+1}(H, ·, ·) on ℝ₊²; the outer price is the time-n price of W with maturity n + 1, and the equality is between numbers for each (s, ŝ); reason: the proof on pp.139–140 prices exactly this claim; the inner random variable depends on ω only through the state at time n + 1
--   - generalization: prices s > 0, ŝ > 0 in b) and c) → all s, ŝ ≥ 0, the whole price part of E = ℝ × ℝ₊²; reason: the book's prices are included, and a) is stated on all of E as printed
--   - encoding: state space E = ℝ × ℝ₊², policies on E → state type ℝ³ and policies on ℝ³, statements on E; reason: a process started in E stays in E, and every measurable decision rule on E extends to ℝ³, so the values on E are the same
--   - encoding: a claim with maturity N only → the maturity is an argument of the value function and the price; reason: c) prices a claim with maturity n + 1 and the model is time-homogeneous
--   - encoding: H = h(S_N, Ŝ_N) a non-negative random variable → h a measurable function on ℝ² with h ≥ 0 on ℝ₊²; reason: g_N must be measurable in a Markov Decision Model (Def. 2.1.1), and the prices stay in ℝ₊²
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.9.4, p.139

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_VH
import Definitions.Def_BauerleRiederMDP_Indifference_Market_IsIndifferencePrice
import Definitions.Def_BauerleRiederMDP_Indifference_Market_v
import Definitions.Def_BauerleRiederMDP_Indifference_Market_dseq

open MeasureTheory

namespace BauerleRiederMDP.Indifference

/-- Theorem 4.9.4 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011),
Theorem 4.9.4, p.139, PDF 153). For the multiperiod financial market:

a) `V^H_n(x, s, ŝ) = -e^{-γx} d_n(s, ŝ)`, where `d_N(s, ŝ) = e^{γh(s, ŝ)}` and
`d_n(s, ŝ) = inf_a 𝔼[e^{-γa(R̃_{n+1}-1)} d_{n+1}(s R̃_{n+1}, ŝ R̂_{n+1})]`; in particular
`V⁰_n(x, s, ŝ) = -e^{-γx} v^{N-n}`.

b) `v_n(H, s, ŝ) = (1/γ) log(d_n(s, ŝ)/v^{N-n})`.

c) `v_n(v_{n+1}(H, s R̃_{n+1}, ŝ R̂_{n+1}), s, ŝ) = v_n(H, s, ŝ)` for `n = 0, 1, …, N - 1`.

**Formalization Note.** `0 ≤ d̂` is the book's `𝒵 := ℝ₊ × ℝ₊` (p.138), the set of the relative
price changes of the multiperiod model. Part b) says that the number on the right is the only solution of the
defining equation of the indifference price, which is what makes "the" price well defined. In
part c) the inner price is the payoff of a claim `W` with maturity `n + 1`, the function
`(s', ŝ') ↦ v_{n+1}(H, s', ŝ')` of the prices at time `n + 1`; `W` is a contingent claim in the
sense of `Claim` (measurable, non-negative on `ℝ₊²`), and the outer `v_n` is its price at time `n`
in the market with maturity `n + 1`. The equality holds between numbers for each `(s, ŝ)`. -/
theorem theorem_4_9_4 (M : Market) (hdhat : 0 ≤ M.dhat) (N : ℕ) (H : Claim) :
    (∀ n, n ≤ N → ∀ x s ŝ : ℝ, 0 ≤ s → 0 ≤ ŝ →
      M.VH N H n x s ŝ = ((-Real.exp (-M.γ * x) * M.dseq N H n s ŝ : ℝ) : EReal)) ∧
    (∀ s ŝ : ℝ, M.dseq N H N s ŝ = Real.exp (M.γ * H s ŝ)) ∧
    (∀ n, n < N → ∀ s ŝ : ℝ, M.dseq N H n s ŝ =
      ⨅ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rt ω - 1)) *
        M.dseq N H (n + 1) (s * M.Rt ω) (ŝ * M.Rh ω) ∂M.P) ∧
    (∀ n, n ≤ N → ∀ x s ŝ : ℝ, 0 ≤ s → 0 ≤ ŝ →
      M.VH N Claim.zero n x s ŝ = ((-Real.exp (-M.γ * x) * M.v ^ (N - n) : ℝ) : EReal)) ∧
    (∀ n, n ≤ N → ∀ s ŝ : ℝ, 0 ≤ s → 0 ≤ ŝ →
      (∀ w : ℝ, M.IsIndifferencePrice N H n s ŝ w ↔
        w = 1 / M.γ * Real.log (M.dseq N H n s ŝ / M.v ^ (N - n))) ∧
      M.indifferencePrice N H n s ŝ =
        1 / M.γ * Real.log (M.dseq N H n s ŝ / M.v ^ (N - n))) ∧
    (∀ n, n < N → ∃ W : Claim,
      (∀ s' ŝ' : ℝ, 0 ≤ s' → 0 ≤ ŝ' → W s' ŝ' = M.indifferencePrice N H (n + 1) s' ŝ') ∧
      ∀ s ŝ : ℝ, 0 ≤ s → 0 ≤ ŝ →
        M.indifferencePrice (n + 1) W n s ŝ = M.indifferencePrice N H n s ŝ) := by sorry

end BauerleRiederMDP.Indifference
