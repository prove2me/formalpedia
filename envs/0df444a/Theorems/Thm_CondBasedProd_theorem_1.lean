-- Prove2me | Theorems.Thm_CondBasedProd_theorem_1
-- name    : CondBasedProd.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:45.884846+00:00
-- url     : https://prove2.me/theorems/581e15e2-2a7d-4495-ae1c-a0714d559050
-- title:
--   Theorem 1, p.12: the optimal production rate decreases in $x$, $t$ and $\lambda$ (corrected: strong set order)
-- statement:
--   Let the model satisfy the standing assumptions, and let $\mathrm{Opt}_\lambda(x,t)$ be the set of optimal production rates. For all $\lambda,\lambda'\ge0$, $t,t'\ge0$ and levels at most $\xi$:
--
--   1. **Extremes.** $\mathrm{Opt}_\lambda(x,t)$ has a greatest element $\bar s^*_\lambda(x,t)$ and a least element $\underline s^*_\lambda(x,t)$.
--   2. **Set monotonicity.** $\mathrm{Opt}$ decreases in the strong set order: for $s\in\mathrm{Opt}_\lambda(x,t)$ and $s'\in\mathrm{Opt}_\lambda(x',t)$ with $x\le x'$, one has $\min(s,s')\in\mathrm{Opt}_\lambda(x',t)$ and $\max(s,s')\in\mathrm{Opt}_\lambda(x,t)$; the same holds for $t\le t'$ between $(x,t)$ and $(x,t')$, and for $\lambda\le\lambda'$ between $\lambda$ and $\lambda'$.
--   3. **Selections.** $\bar s^*$ and $\underline s^*$ are each decreasing in $x$, in $t$ and in $\lambda$.
--   4. **Optimality.** For every measurable selection $\sigma$ of $\mathrm{Opt}_\lambda$, the feedback policy of $\sigma$ from $(x,t)$ attains $J^*_\lambda(x,t)$, and $\bar s^*_\lambda$, $\underline s^*_\lambda$ are measurable selections.
--
--   Here $J^*_\lambda$ is the value of the stochastic control problem (1) and $\mathrm{Opt}_\lambda(\xi,t)=\{0\}$. A system that is more deteriorated, further from maintenance, or subject to a higher base rate is run more slowly; when maximizers are unique, clause 3 is the printed statement for the unique rate $s^*_\lambda(x,t)$.
--
--   Differences from the source:
--   - correction: s*_λ(x,t), any solution of (2), is decreasing in x, t and λ → Opt_λ decreases in the strong set order, and its greatest and least selections decrease; reason: maximizers need not be unique: on S = [0,1], r(s) = f(s) = s, ξ = 1, c_m = (0,1), λ = 1 every s is optimal at every state, so the selection min(t,1) is optimal and increasing in t
--   - correction: (2) with second branch 0 as the characterization of J* → J* is the value of (1), where the failed system earns r(0); reason: with printed (2) the goal fails when r(0) < 0: S = [0,1], r(s) = s − ½, f(s) = s², ξ = 1, c_m = (0,5), λ = 1 makes the bracket maximizer rise in t; under (1) Δ² = 25 + t/2 and it falls
--   - generalization: only monotonicity of s* → also existence of extremes and attainment of J* by every measurable selection; reason: clause 3 and clause 2 are the source claim; clauses 1 and 4 are what the source asserts of s* on p.10, made explicit
--   - encoding: Opt at x = ξ is not separately defined in (2) → Opt_λ(ξ,t) = {0}, and Δ_λ(ξ,·) is never read; reason: "the only admissible action is s = 0" (App. A.1, p.34)
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - reading: 𝒰, "all admissible non-anticipating production policies" (p.9), class not specified further → deterministic measurable rules of the past increment times; reason: the internal-history reading, as for a Markovian intensity control problem (p.10); randomized rules would not change J*
--   - reading: the constraint ∫dY ≤ ξ − X_t (p.9) alone would allow s > 0 with f(s) = 0 at x = ξ → the rate is 0 once failed (exactly ξ − x clocks are used); reason: "the system is turned off" (p.9), "the only admissible action is s = 0" (App. A.1, p.34)
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
--   - encoding: a Poisson process whose rate is instantaneously λ f(s) (p.8) → the (j+1)-st increment comes when ∫ λ f(s) dv since the j-th reaches an Exp(1) clock E_j; reason: the standard time-change construction of the same counting process, on the published clock law
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Theorem 1, p.12; App. A.9, pp.39–40

import Mathlib
import Definitions.Def_CondBasedProd_IsOptRate
import Definitions.Def_CondBasedProd_Selection

open Set

namespace CondBasedProd

/-- **Theorem 1** (Drent, Drent & Arts, *Condition-Based Production for Stochastically Deteriorating
Systems*, arXiv:2308.07507v2, p.12): the optimal production rate `s*_λ(x,t)` is decreasing in `x`, `t`
and `λ`.

For every model under the standing assumptions, with `λ, λ' ≥ 0`, `t, t' ≥ 0`, levels at most `ξ`:

1. `Opt_λ(x,t)` has a greatest element `s̄*_λ(x,t)` and a least element `s̲*_λ(x,t)`.
2. `Opt_λ(x,t)` decreases in the strong set order in each of `x`, `t`, `λ`.
3. `s̄*` and `s̲*` are each decreasing in `x`, in `t` and in `λ`.
4. The feedback policy of every measurable selection of `Opt` attains `J*_λ` from every state, and
   `s̄*`, `s̲*` are measurable selections.

**Formalization Note.** Maximizers need not be unique: at `𝒮 = [0,1]`, `r(s) = f(s) = s`, `ξ = 1`,
`c_m = (0,1)`, `λ = 1` every `s` is optimal at every state, so the reading "every selection of (2) is
decreasing" is false, and the strong-set-order form above is the strongest true reading. `J*` is the
value of the stochastic problem (1), not of an arbitrary solution of (2). `Opt_λ(ξ,t) = {0}`. -/
theorem theorem_1 (M : Model) : (∀ lam, 0 ≤ lam → ∀ x ≤ M.ξ, ∀ t, 0 ≤ t → IsGreatest (optRateSet M lam x t) (optRateMax M lam x t) ∧ IsLeast (optRateSet M lam x t) (optRateMin M lam x t)) ∧ (∀ lam, 0 ≤ lam → ∀ x x', x ≤ x' → x' ≤ M.ξ → ∀ t, 0 ≤ t → StrongSetBelow (optRateSet M lam x' t) (optRateSet M lam x t)) ∧ (∀ lam, 0 ≤ lam → ∀ x ≤ M.ξ, ∀ t t', 0 ≤ t → t ≤ t' → StrongSetBelow (optRateSet M lam x t') (optRateSet M lam x t)) ∧ (∀ lam lam', 0 ≤ lam → lam ≤ lam' → ∀ x ≤ M.ξ, ∀ t, 0 ≤ t → StrongSetBelow (optRateSet M lam' x t) (optRateSet M lam x t)) ∧ (∀ lam, 0 ≤ lam → ∀ x x', x ≤ x' → x' ≤ M.ξ → ∀ t, 0 ≤ t → optRateMax M lam x' t ≤ optRateMax M lam x t ∧ optRateMin M lam x' t ≤ optRateMin M lam x t) ∧ (∀ lam, 0 ≤ lam → ∀ x ≤ M.ξ, AntitoneOn (optRateMax M lam x) (Ici 0) ∧ AntitoneOn (optRateMin M lam x) (Ici 0)) ∧ (∀ x ≤ M.ξ, ∀ t, 0 ≤ t → AntitoneOn (fun lam => optRateMax M lam x t) (Ici 0) ∧ AntitoneOn (fun lam => optRateMin M lam x t) (Ici 0)) ∧ (∀ lam, 0 ≤ lam → ∀ σ : Selection M, (∀ x ≤ M.ξ, ∀ t, 0 ≤ t → IsOptRate M lam x t (σ.rate x t)) → ∀ x ≤ M.ξ, ∀ t, 0 ≤ t → value M lam (σ.feedback x t) x t = optValue M lam x t) ∧ (∀ lam, 0 ≤ lam → (∃ σ : Selection M, σ.rate = optRateMax M lam) ∧ ∃ σ : Selection M, σ.rate = optRateMin M lam) := by sorry

end CondBasedProd
