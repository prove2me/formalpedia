-- Prove2me | Theorems.Thm_BNS2000_theorem_4_3_and_4_4
-- name    : BNS2000.theorem_4_3_and_4_4
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:08:34.32707+00:00
-- url     : https://prove2.me/theorems/5e24e9ec-f0f3-47bf-a0d2-46a45e19ddf5
-- title:
--   Register-Machine Evaluation and Linear Step/Register Bounds for R-Free RS-Terms (Theorem 4.3 & Corollary 4.4)
-- statement:
--   Theorem 4.3 and Corollary 4.4 (pp. 23-24): Every `R`-free `RS`-term `t` of ground type evaluated on numeral environment `n⃗` via `NFEval` computes its numeral normal form `nf(t[n⃗/x⃗])` in at most `2|t|` steps using at most `|t|` registers of length at most `|t| + max |n_i|`.
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Section 4, Theorem 4.3 and Corollary 4.4, pp. 23-24.

import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 4.3 and Corollary 4.4 (Base Normalisation)** (Section 4, p. 24):
1. (**Theorem 4.3**): For every `R`-free `RS`-term `t` of ground type and numeral environment
   `n⃗; x⃗` (`IsNumeralEnv env`) such that `FV(t) ⊆ x⃗`:
   (i) the register-machine algorithm `nf(t; n⃗; x⃗)` (`NFEval`) computes the numeral normal form
       `out = nf(t[n⃗/x⃗])` in at most `2 |t|` steps,
   (ii) the number of used registers is `≤ |t| + #n⃗`, and
   (iii) the maximum length `maxLen` of any term occurring in the computation satisfies
         `maxLen ≤ |t| + max |nᵢ|`.
2. (**Corollary 4.4, Base Normalisation**): For every closed `R`-free `RS`-term `t` of ground
   type, the numeral `nf(t)` is computed in at most `2 |t|` steps using `≤ |t|` registers,
   with every term occurring in the computation having length `≤ |t|`. -/
theorem theorem_4_3_and_4_4 :
    (∀ (t : Term) (τ : Ty) (env : List (Var × Term)),
      IsRSTerm t →
      isRFree t = true →
      HasType t τ →
      τ.isGround = true →
      IsNumeralEnv env →
      (∀ v ∈ freeVars t, v ∈ env.map Prod.fst) →
      ∃ (out : Term) (steps regs maxLen : Nat),
        NFEval t env out steps regs maxLen ∧
        IsNormalFormOf (substEnv t env) out ∧
        isNumeral out = true ∧
        steps ≤ 2 * termLength t ∧
        regs ≤ termLength t + env.length ∧
        maxLen ≤ termLength t + maxEnvTermLength env) ∧
    (∀ (t : Term) (τ : Ty),
      IsRSTerm t →
      isRFree t = true →
      IsClosed t →
      HasType t τ →
      τ.isGround = true →
      ∃ (out : Term) (steps regs maxLen : Nat),
        NFEval t [] out steps regs maxLen ∧
        IsNormalFormOf t out ∧
        isNumeral out = true ∧
        steps ≤ 2 * termLength t ∧
        regs ≤ termLength t ∧
        maxLen ≤ termLength t) := by
  sorry

end BNS2000
