-- Prove2me | Theorems.Thm_CondBasedProd_lambda_delta_increasing
-- name    : CondBasedProd.lambda_delta_increasing
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:06.140196+00:00
-- url     : https://prove2.me/theorems/444e7591-5887-4404-a17d-f37eccf85cf0
-- title:
--   App. A.9, p.40: $\lambda\Delta_\lambda(x,t)$ is increasing in $\lambda$ (corrected: Proposition 4 is false)
-- statement:
--   Let the model satisfy the standing assumptions, $0\le\lambda\le\lambda'$, $x<\xi$, $t\ge0$. Then
--   $$
--   \lambda\,\Delta_\lambda(x,t)\le\lambda'\,\Delta_{\lambda'}(x,t).
--   $$
--
--   This is the continuous-time form of the condition "$\lambda J^*_\lambda(x,k-1)$ is submodular in $(x,\lambda)$" of App. A.9, the only property of the $\lambda$ dependence the proof of Theorem 1 needs. The stronger Proposition 4 of the source, that $\Delta_\lambda(x,t)$ itself increases in $\lambda$, is false, and is not stated in this mission.
--
--   Differences from the source:
--   - correction: Proposition 4: J_λ(x,t) submodular in (x,λ), i.e. Δ_λ(x,t) increasing in λ, from which A.9 derives that λJ* is submodular → λΔ_λ(x,t) is increasing in λ, stated directly; reason: Proposition 4 fails on S = [0,1], r(s) = f(s) = s, ξ = 1, c_m ≡ 0: Δ_λ(0,t) = (1 − e^{−λt})/λ decreases in λ, while λΔ_λ(0,t) = 1 − e^{−λt} increases
--   - encoding: the discretized condition at (x, k − 1) with x ∈ 𝒳 → the continuous-time J* at (x,t), x < ξ; reason: the discretization (22) of the source converges to J*; Δ_λ(ξ,·) is undefined
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - reading: 𝒰, "all admissible non-anticipating production policies" (p.9), class not specified further → deterministic measurable rules of the past increment times; reason: the internal-history reading, as for a Markovian intensity control problem (p.10); randomized rules would not change J*
--   - reading: the constraint ∫dY ≤ ξ − X_t (p.9) alone would allow s > 0 with f(s) = 0 at x = ξ → the rate is 0 once failed (exactly ξ − x clocks are used); reason: "the system is turned off" (p.9), "the only admissible action is s = 0" (App. A.1, p.34)
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
--   - encoding: a Poisson process whose rate is instantaneously λ f(s) (p.8) → the (j+1)-st increment comes when ∫ λ f(s) dv since the j-th reaches an Exp(1) clock E_j; reason: the standard time-change construction of the same counting process, on the published clock law
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, App. A.9, p.40 (replacing Proposition 4, p.12)

import Mathlib
import Definitions.Def_CondBasedProd_Policy

namespace CondBasedProd

/-- **`λ Δ_λ(x,t)` is increasing in `λ`** (arXiv:2308.07507v2, App. A.9, p.40): the continuous-time form
of "`λ J*_λ(x, k−1)` is submodular in `(x,λ)`", the condition the proof of Theorem 1 needs.

**Formalization Note.** This replaces **Proposition 4** (p.12), which is false: for `𝒮 = [0,1]`,
`r(s) = f(s) = s`, `ξ = 1`, `c_m ≡ 0` one has `Δ_λ(0,t) = (1 − e^{−λt})/λ`, decreasing in `λ`, while
`λ Δ_λ(0,t) = 1 − e^{−λt}` increases. -/
theorem lambda_delta_increasing (M : Model) (lam lam' : ℝ) (hlam : 0 ≤ lam) (hle : lam ≤ lam') (x : ℕ) (hx : x < M.ξ) (t : ℝ) (ht : 0 ≤ t) : lam * delta M lam x t ≤ lam' * delta M lam' x t := by sorry

end CondBasedProd
