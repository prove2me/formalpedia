-- Prove2me | Theorems.Thm_CondBasedProd_optimal_selection_attains
-- name    : CondBasedProd.optimal_selection_attains
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:08.380096+00:00
-- url     : https://prove2.me/theorems/5c1712a7-67f3-4906-b2db-7e57cd16de32
-- title:
--   Lemma 1 discussion, p.10: every measurable selection of the optimal rates attains $J^*_\lambda$
-- statement:
--   Let the model satisfy the standing assumptions and let $\lambda\ge0$. Let $\sigma$ be a measurable selection with $\sigma(x,t)\in\mathrm{Opt}_\lambda(x,t)$ for all $x\le\xi$, $t\ge0$. Then for all $x\le\xi$, $t\ge0$, the feedback policy of $\sigma$ from the state $(x,t)$ attains the optimal expected profit:
--   $$
--   J^{\sigma}_\lambda(x,t)=J^*_\lambda(x,t).
--   $$
--
--   This gives "the optimal production rate for state $(x,t)$" of the source its meaning: a rate at a single state is optimal because following such rates is optimal.
--
--   Differences from the source:
--   - reading: "s*_λ(x,t) is the optimal production rate for state (x,t)" → the feedback policy of every measurable selection of the maximizers of (2) attains J*; reason: a rate at one state can be optimal only through a policy, and a policy must be measurable; maximizers need not be unique, so every selection is covered
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - reading: 𝒰, "all admissible non-anticipating production policies" (p.9), class not specified further → deterministic measurable rules of the past increment times; reason: the internal-history reading, as for a Markovian intensity control problem (p.10); randomized rules would not change J*
--   - reading: the constraint ∫dY ≤ ξ − X_t (p.9) alone would allow s > 0 with f(s) = 0 at x = ξ → the rate is 0 once failed (exactly ξ − x clocks are used); reason: "the system is turned off" (p.9), "the only admissible action is s = 0" (App. A.1, p.34)
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
--   - encoding: a Poisson process whose rate is instantaneously λ f(s) (p.8) → the (j+1)-st increment comes when ∫ λ f(s) dv since the j-th reaches an Exp(1) clock E_j; reason: the standard time-change construction of the same counting process, on the published clock law
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Lemma 1 discussion, p.10

import Mathlib
import Definitions.Def_CondBasedProd_IsOptRate
import Definitions.Def_CondBasedProd_Selection

namespace CondBasedProd

/-- **Optimal selections attain `J*`** (arXiv:2308.07507v2, p.10: "`s*_λ(x,t)` is the optimal
production rate for state `(x,t)`"): the feedback policy of every measurable selection of the optimal
rates attains the optimal expected profit from every state. -/
theorem optimal_selection_attains (M : Model) (lam : ℝ) (hlam : 0 ≤ lam) (σ : Selection M) (hσ : ∀ x ≤ M.ξ, ∀ t, 0 ≤ t → IsOptRate M lam x t (σ.rate x t)) (x : ℕ) (hx : x ≤ M.ξ) (t : ℝ) (ht : 0 ≤ t) : value M lam (σ.feedback x t) x t = optValue M lam x t := by sorry

end CondBasedProd
