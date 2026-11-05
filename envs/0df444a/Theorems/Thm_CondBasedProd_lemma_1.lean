-- Prove2me | Theorems.Thm_CondBasedProd_lemma_1
-- name    : CondBasedProd.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:47.845194+00:00
-- url     : https://prove2.me/theorems/bf8c90f8-4c51-40fe-8797-6859eddb1c2e
-- title:
--   Lemma 1, p.10: $J^*_\lambda$ solves the HJB system (corrected: $\partial_tJ^*(\xi,t)=r(0)$)
-- statement:
--   Let the model satisfy the standing assumptions and let $\lambda\ge0$. The optimal expected profit $J^*_\lambda$ of the stochastic problem (1) satisfies, for $t\ge 0$,
--   $$
--   \frac{\partial J^*_\lambda(x,t)}{\partial t}=\begin{cases}\max_{s\in\mathcal S}\bigl[r(s)-\lambda f(s)\Delta_\lambda(x,t)\bigr],&x\in\{0,\dots,\xi-1\},\\ r(0),&x=\xi,\end{cases}
--   $$
--   with $J^*_\lambda(x,0)=-c_m(x)$ for all $x\in\mathcal X$. In addition, for $x\le\xi$ and $t\ge0$:
--
--   1. the realized profit of every policy is integrable;
--   2. the values $J^u_\lambda(x,t)$ are bounded above in $u$.
--
--   This is the bridge between the stochastic control problem and the ordinary differential system on which the structural results rest.
--
--   Differences from the source:
--   - correction: (2) at x = ξ: ∂_t J*_λ(ξ,t) = 0 → ∂_t J*_λ(ξ,t) = r(0); reason: under (1) the failed system runs at s = 0 and earns r(0), so J*_λ(ξ,t) = r(0) t − c_m(ξ); with S = [0,1], r(s) = s − 2, f(s) = s, ξ = 1 the printed branch fails at x = ξ. Same when r(0) = 0
--   - generalization: Lemma 1 states the HJB equation and boundary condition → also integrability of the profit and boundedness of the policy values; reason: the extra clauses are true and fix the meaning of the integral and supremum in (1); the HJB clause is the source claim
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - reading: 𝒰, "all admissible non-anticipating production policies" (p.9), class not specified further → deterministic measurable rules of the past increment times; reason: the internal-history reading, as for a Markovian intensity control problem (p.10); randomized rules would not change J*
--   - reading: the constraint ∫dY ≤ ξ − X_t (p.9) alone would allow s > 0 with f(s) = 0 at x = ξ → the rate is 0 once failed (exactly ξ − x clocks are used); reason: "the system is turned off" (p.9), "the only admissible action is s = 0" (App. A.1, p.34)
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
--   - encoding: a Poisson process whose rate is instantaneously λ f(s) (p.8) → the (j+1)-st increment comes when ∫ λ f(s) dv since the j-th reaches an Exp(1) clock E_j; reason: the standard time-change construction of the same counting process, on the published clock law
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Lemma 1, display (2), p.10

import Mathlib
import Definitions.Def_CondBasedProd_Policy
import Definitions.Def_CondBasedProd_IsHJBSolution

open MeasureTheory
open GVRPricing.FixedPrice (clockLaw)

namespace CondBasedProd

/-- **Lemma 1** (arXiv:2308.07507v2, p.10), corrected at `x = ξ`: `J*_λ` of the stochastic problem (1)
solves the HJB system (2) with boundary values `−c_m`, the derivative at `x = ξ` being `r(0)`.

The two further clauses make the Bochner integral and the real supremum in `value` and `optValue`
mean what they say: for `x ≤ ξ`, `t ≥ 0`, the profit of every policy is integrable and the policy
values are bounded above.

**Formalization Note.** The correction matters only when `r(0) < 0`. By definition (1), the failed
system earns `r(0)` until maintenance, so `J*_λ(ξ,t) = r(0) t − c_m(ξ)`. -/
theorem lemma_1 (M : Model) (lam : ℝ) (hlam : 0 ≤ lam) : IsHJBSolution M lam (optValue M lam) ∧ (∀ x ≤ M.ξ, ∀ t, 0 ≤ t → BddAbove (Set.range fun u : Policy M => value M lam u x t)) ∧ ∀ (u : Policy M), ∀ x ≤ M.ξ, ∀ t, 0 ≤ t → Integrable (profit M lam u x t) clockLaw := by sorry

end CondBasedProd
