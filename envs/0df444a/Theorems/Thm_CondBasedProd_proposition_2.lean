-- Prove2me | Theorems.Thm_CondBasedProd_proposition_2
-- name    : CondBasedProd.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:57.097899+00:00
-- url     : https://prove2.me/theorems/65831cb9-cc21-471f-abd6-4f525eeafbd7
-- title:
--   Proposition 2, p.11: $\Delta_\lambda(x,t)$ is increasing in $t$
-- statement:
--   Let the model satisfy the standing assumptions, $\lambda\ge0$, and $x<\xi$. Then $t\mapsto\Delta_\lambda(x,t)$ is increasing on $[0,\infty)$.
--
--   The marginal value of less deterioration grows with the time remaining until maintenance. Through the bracket of (2), this is what makes the optimal rate decrease in $t$.
--
--   Differences from the source:
--   - encoding: for all x ∈ 𝒳 → for x < ξ; reason: Δ_λ(ξ,·) is undefined: the level ξ + 1 does not exist; no instance is lost
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - reading: 𝒰, "all admissible non-anticipating production policies" (p.9), class not specified further → deterministic measurable rules of the past increment times; reason: the internal-history reading, as for a Markovian intensity control problem (p.10); randomized rules would not change J*
--   - reading: the constraint ∫dY ≤ ξ − X_t (p.9) alone would allow s > 0 with f(s) = 0 at x = ξ → the rate is 0 once failed (exactly ξ − x clocks are used); reason: "the system is turned off" (p.9), "the only admissible action is s = 0" (App. A.1, p.34)
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
--   - encoding: a Poisson process whose rate is instantaneously λ f(s) (p.8) → the (j+1)-st increment comes when ∫ λ f(s) dv since the j-th reaches an Exp(1) clock E_j; reason: the standard time-change construction of the same counting process, on the published clock law
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Proposition 2, p.11

import Mathlib
import Definitions.Def_CondBasedProd_Policy

open Set

namespace CondBasedProd

/-- **Proposition 2** (arXiv:2308.07507v2, p.11): `Δ_λ(x,t)` is increasing in `t`.

**Formalization Note.** Stated for `x < ξ`, since `Δ_λ(ξ,·)` is undefined (the paper prints `x ∈ 𝒳`). -/
theorem proposition_2 (M : Model) (lam : ℝ) (hlam : 0 ≤ lam) (x : ℕ) (hx : x < M.ξ) : MonotoneOn (delta M lam x) (Ici 0) := by sorry

end CondBasedProd
