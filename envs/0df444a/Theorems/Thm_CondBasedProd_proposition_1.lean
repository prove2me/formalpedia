-- Prove2me | Theorems.Thm_CondBasedProd_proposition_1
-- name    : CondBasedProd.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:00.763561+00:00
-- url     : https://prove2.me/theorems/17c179a8-0531-4b46-a395-55e260b08f3d
-- title:
--   Proposition 1, p.11: $J^*_\lambda(x,t)$ is concave in $x$
-- statement:
--   Let the model satisfy the standing assumptions, $\lambda\ge0$, $t\ge0$, and $x+2\le\xi$. Then
--   $$
--   \Delta_\lambda(x,t)\le\Delta_\lambda(x+1,t),
--   $$
--   that is, $J^*_\lambda(\cdot,t)$ is concave on $\mathcal X$. Expected profit falls ever faster as the deterioration level approaches failure. Through the bracket of (2), this inequality is what makes the optimal rate decrease in $x$.
--
--   Differences from the source:
--   - encoding: concave in x on 𝒳 → Δ_λ(x,t) ≤ Δ_λ(x+1,t) for x + 2 ≤ ξ; reason: the discrete concavity Δ²_λ ≤ 0 of App. A.3, p.34; same statement
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - reading: 𝒰, "all admissible non-anticipating production policies" (p.9), class not specified further → deterministic measurable rules of the past increment times; reason: the internal-history reading, as for a Markovian intensity control problem (p.10); randomized rules would not change J*
--   - reading: the constraint ∫dY ≤ ξ − X_t (p.9) alone would allow s > 0 with f(s) = 0 at x = ξ → the rate is 0 once failed (exactly ξ − x clocks are used); reason: "the system is turned off" (p.9), "the only admissible action is s = 0" (App. A.1, p.34)
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
--   - encoding: a Poisson process whose rate is instantaneously λ f(s) (p.8) → the (j+1)-st increment comes when ∫ λ f(s) dv since the j-th reaches an Exp(1) clock E_j; reason: the standard time-change construction of the same counting process, on the published clock law
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Proposition 1, p.11; App. A.3, p.34

import Mathlib
import Definitions.Def_CondBasedProd_Policy

namespace CondBasedProd

/-- **Proposition 1** (arXiv:2308.07507v2, p.11): `J*_λ(x,t)` is concave in `x` for all `t ≥ 0` and
`λ ≥ 0`, in the form used by the proof (App. A.3, p.34): `Δ²_λ(x,t) = Δ_λ(x,t) − Δ_λ(x+1,t) ≤ 0` for
`x ≤ ξ − 2`. -/
theorem proposition_1 (M : Model) (lam : ℝ) (hlam : 0 ≤ lam) (x : ℕ) (hx : x + 2 ≤ M.ξ) (t : ℝ) (ht : 0 ≤ t) : delta M lam x t ≤ delta M lam (x + 1) t := by sorry

end CondBasedProd
