-- Prove2me | Theorems.Thm_BankLiability_default_boundary_eq_3
-- name    : BankLiability.default_boundary_eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:12.494731+00:00
-- url     : https://prove2.me/theorems/b8aedac5-a81d-4253-a0ad-7eb8b2d91bd6
-- title:
--   Eq. (3): $V_d$ maximizes equity value over default boundaries, gives zero equity, and increases in each liability
-- statement:
--   Fix parameters in Table 1's ranges. For an insurance premium $I$, a deposit cost $C_D$ and a nondeposit coupon $C_B$ with total coupon $C=I+C_D+C_B>0$, let
--
--   $$V_d=(1-\tau)\frac{\lambda}{1+\lambda}\cdot\frac{I+C_D+C_B}{r} \qquad (3)$$
--
--   and, for an asset value $V>0$ and a default boundary $L\in(0,V]$, let $E_L(V)=V-(1-\tau)\frac{C}{r}\big(1-(L/V)^\lambda\big)-L\,(L/V)^\lambda$ be the equity value when the bank is liquidated at $L$. If $V\ge V_d$, then:
--
--   1. $0<V_d\le V$, and $E_{V_d}(V)>E_L(V)$ for every other boundary $L\in(0,V]$: defaulting at $V_d$ maximizes the equity value;
--   2. $E_{V_d}(V_d)=0$: $V_d$ is the asset value at which the equity value is zero;
--   3. $V_d$ is strictly increasing in each of $I$, $C_D$ and $C_B$ when the other two are fixed.
--
--   This is the endogenous default of the equity holders: they keep the bank running and default when equity is worth zero, and the formula (3) shows how each liability pushes the default boundary up.
--
--   Differences from the source:
--   - reading: the equity value for a default boundary (derivation in the Online Appendix, not held) → E_L = V − (1−τ)C/r·(1 − (L/V)^λ) − L(L/V)^λ, eq. (16) with no restructuring; reason: the model's closed-form state-price level, matching the dividend δV − (1−τ)(I + C_D + C_B) of p.4
--   - reading: "this default strategy maximizes equity value" → V_d is the strict maximizer of E_L over boundaries L ∈ (0, V], for every V ≥ V_d; reason: default strategies are boundaries at which the bank is liquidated, as in (3) and (16)
--   - encoding: liabilities I, C_D, C_B → total coupon C > 0 assumed; reason: with C = 0 there is no debt to default on and V_d = 0 is not a boundary in (0, V]
--   - generalization: I, C_D, C_B are liabilities, so nonnegative → arbitrary reals with C > 0; reason: nothing in the statement uses their signs, and it specializes to nonnegative liabilities
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.2, eq. (3) and the paragraph before and after it, p.6

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam
import Definitions.Def_BankLiability_Model

namespace BankLiability

/-- **Equation (3): V_d is the equity-maximizing default boundary, gives zero equity value, and
increases in each liability.**
Sundaresan–Wang, *Strategic Bank Liability Structure Under Capital Requirements*, Management
Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.2, eq. (3), p.6: "The equity
holders default on the bank's debt obligations and liquidate assets if the equity value reaches
zero because this default strategy maximizes equity value [...] The endogenous default boundary
is the asset value, denoted by V_d, that gives zero equity value. [...]
V_d = (1−τ) λ/(1+λ) · (I + C_D + C_B)/r, (3) [...] The formula indicates that the endogenous
boundary is an increasing function of each liability."

For a total coupon `C = I + C_D + C_B > 0`, `V_d` its boundary (3), and asset value `V > 0` with
`V_d ≤ V`:
1. `0 < V_d ≤ V`, and among all default boundaries `L ∈ (0, V]` the boundary `V_d` gives the
   strictly largest equity value `equityGivenBoundary P V C L`;
2. at asset value `V = V_d`, liquidating at `V_d` gives zero equity value;
3. `V_d` is strictly increasing in each of `I`, `C_D`, `C_B` (the other two fixed).

**Formalization Note.** The equity value for a default boundary `L` is (16), p.15, with no
restructuring, at the state-price level (`equityGivenBoundary`). -/
theorem default_boundary_eq_3 (P : Params) (V I CD CB : ℝ) (hV : 0 < V)
    (hC : 0 < I + CD + CB) (hVd : defaultBoundaryOf P I CD CB ≤ V) :
    (defaultBoundaryOf P I CD CB ∈ Set.Ioc 0 V ∧
      ∀ L ∈ Set.Ioc 0 V, L ≠ defaultBoundaryOf P I CD CB →
        equityGivenBoundary P V (I + CD + CB) L <
          equityGivenBoundary P V (I + CD + CB) (defaultBoundaryOf P I CD CB)) ∧
    equityGivenBoundary P (defaultBoundaryOf P I CD CB) (I + CD + CB)
        (defaultBoundaryOf P I CD CB) = 0 ∧
    StrictMono (fun I' => defaultBoundaryOf P I' CD CB) ∧
    StrictMono (fun CD' => defaultBoundaryOf P I CD' CB) ∧
    StrictMono (fun CB' => defaultBoundaryOf P I CD CB') := by sorry

end BankLiability
