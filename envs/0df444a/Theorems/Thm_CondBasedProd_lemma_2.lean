-- Prove2me | Theorems.Thm_CondBasedProd_lemma_2
-- name    : CondBasedProd.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:57.266657+00:00
-- url     : https://prove2.me/theorems/22dd5cef-b790-4625-b05b-b4b00c3a1fd4
-- title:
--   Lemma 2, p.11: $J^*_\lambda$ decreases in $x$ and $\lambda$ (corrected: $J^*_\lambda-r(0)t$ increases in $t$)
-- statement:
--   Let the model satisfy the standing assumptions. Then:
--
--   1. for $\lambda\ge0$, $x<\xi$, $t\ge0$: $J^*_\lambda(x+1,t)\le J^*_\lambda(x,t)$;
--   2. for $\lambda\ge0$, $x\le\xi$: $t\mapsto J^*_\lambda(x,t)-r(0)\,t$ is increasing on $[0,\infty)$;
--   3. for $0\le\lambda\le\lambda'$, $x\le\xi$, $t\ge0$: $J^*_{\lambda'}(x,t)\le J^*_\lambda(x,t)$.
--
--   When $r(0)=0$, the second clause is the printed statement that $J^*_\lambda$ increases in the time to maintenance.
--
--   Differences from the source:
--   - correction: J*_λ(x,t) is increasing in t → J*_λ(x,t) − r(0) t is increasing in t; reason: with S = [0,1], r(s) = s − 2, f(s) = s every J*(x,·) has derivative ≤ −1, though r(0) < 0 is allowed by Assumption 1; the Lean form is the printed claim when r(0) = 0
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - reading: 𝒰, "all admissible non-anticipating production policies" (p.9), class not specified further → deterministic measurable rules of the past increment times; reason: the internal-history reading, as for a Markovian intensity control problem (p.10); randomized rules would not change J*
--   - reading: the constraint ∫dY ≤ ξ − X_t (p.9) alone would allow s > 0 with f(s) = 0 at x = ξ → the rate is 0 once failed (exactly ξ − x clocks are used); reason: "the system is turned off" (p.9), "the only admissible action is s = 0" (App. A.1, p.34)
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
--   - encoding: a Poisson process whose rate is instantaneously λ f(s) (p.8) → the (j+1)-st increment comes when ∫ λ f(s) dv since the j-th reaches an Exp(1) clock E_j; reason: the standard time-change construction of the same counting process, on the published clock law
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Lemma 2, p.11

import Mathlib
import Definitions.Def_CondBasedProd_Policy

open Set

namespace CondBasedProd

/-- **Lemma 2** (arXiv:2308.07507v2, p.11), corrected in `t`: `J*_λ(x,t)` is decreasing in `x`,
`J*_λ(x,t) − r(0) t` is increasing in `t`, and `J*_λ(x,t)` is decreasing in `λ`.

**Formalization Note.** The printed claim "increasing in `t`" is false when `r(0) < 0` (for
`r(s) = s − 2`, `f(s) = s`, `𝒮 = [0,1]` every `J*(x,·)` is strictly decreasing). The form here is the
printed claim when `r(0) = 0`. -/
theorem lemma_2 (M : Model) : (∀ lam, 0 ≤ lam → ∀ x < M.ξ, ∀ t, 0 ≤ t → optValue M lam (x + 1) t ≤ optValue M lam x t) ∧ (∀ lam, 0 ≤ lam → ∀ x ≤ M.ξ, MonotoneOn (fun t => optValue M lam x t - M.r 0 * t) (Ici 0)) ∧ (∀ lam lam', 0 ≤ lam → lam ≤ lam' → ∀ x ≤ M.ξ, ∀ t, 0 ≤ t → optValue M lam' x t ≤ optValue M lam x t) := by sorry

end CondBasedProd
