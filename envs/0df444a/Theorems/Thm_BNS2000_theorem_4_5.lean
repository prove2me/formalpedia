-- Prove2me | Theorems.Thm_BNS2000_theorem_4_5
-- name    : BNS2000.theorem_4_5
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:08:45.000136+00:00
-- url     : https://prove2.me/theorems/5eb076ec-d2e4-4bc5-9e1f-e3de47f2bb7e
-- title:
--   Elimination of Recursors from RS-Terms with Polynomial Length Bound (Theorem 4.5)
-- statement:
--   Theorem 4.5 (pp. 25-26): For every `RS`-term `t` whose free variables are ground, there is a polynomial `q_t` such that for any closed `R`-free `RS`-terms `n⃗`, `t[n⃗/x⃗]` is equivalent to an `R`-free `RS`-term `rf_t(n⃗)` of length at most `q_t(∑ |n_i|)`.
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Section 4, Theorem 4.5, pp. 25-26.

import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 4.5 (`R`-Elimination)** (Section 4, p. 24):
Let `t` be an `RS`-term of safe or ground type `τ`. Then there exists a univariate polynomial
`q_t : Nat → Nat` (`IsUnivariatePoly q_t`) such that for every environment `n⃗; x⃗` of closed
ground-type `R`-free `RS`-terms (`IsClosedGroundRFreeRSEnv env`) with `FV(t[n⃗/x⃗])` all safe,
there exists an `R`-free `RS`-term `rf_t` equivalent to `t[n⃗/x⃗]` (with `FV(rf_t) ⊆ FV(t[n⃗/x⃗])`
and `|rf_t| ≤ q_t(∑ |nᵢ|)`) such that if `τ` is ground and `t[n⃗/x⃗]` is closed, `rf_t`
normalizes via `NFEval` in at most `2 · q_t(∑ |nᵢ|)` steps using at most `q_t(∑ |nᵢ|)` registers. -/
theorem theorem_4_5
    (t : Term) (τ : Ty)
    (ht : IsRSTerm t)
    (hτ : HasType t τ)
    (hSafeOrGround : τ.isSafe = true ∨ τ.isGround = true) :
    ∃ q_t : Nat → Nat,
      IsUnivariatePoly q_t ∧
      ∀ env : List (Var × Term),
        IsClosedGroundRFreeRSEnv env →
        (∀ v ∈ freeVars (substEnv t env), v.ty.isSafe = true) →
        ∃ rf_t : Term,
          IsRSTerm rf_t ∧
          isRFree rf_t = true ∧
          HasType rf_t τ ∧
          TermEquiv rf_t (substEnv t env) ∧
          (∀ v ∈ freeVars rf_t, v ∈ freeVars (substEnv t env)) ∧
          termLength rf_t ≤ q_t (sumEnvTermLength env) := by
  sorry

end BNS2000
