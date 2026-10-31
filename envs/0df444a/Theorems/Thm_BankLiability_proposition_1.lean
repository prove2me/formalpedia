-- Prove2me | Theorems.Thm_BankLiability_proposition_1
-- name    : BankLiability.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:40.142512+00:00
-- url     : https://prove2.me/theorems/bd346baa-e347-4c75-a22b-a14dbccee215
-- title:
--   Proposition 1: a liability structure with $V_d<V_b$ is suboptimal
-- statement:
--   Fix parameters in Table 1's ranges and an asset value $V>0$. For a liability structure $(D,C_B)$ write $V_b$ for its regulatory total capital boundary, $V_d$ for its endogenous default boundary and $F(D,C_B)$ for the total bank value of the shareholders.
--
--   1. If $(D,C_B)$ is feasible and $V_d<V_b$, then there is a coupon $C_B'>C_B$ such that $(D,C_B')$ is feasible, the nondeposit debt value $B$ of $(D,C_B')$ is strictly larger than that of $(D,C_B)$, and
--   $$F(D,C_B')>F(D,C_B):$$
--   the bank increases its value by increasing nondeposit debt.
--   2. Consequently every strategic liability structure satisfies $V_b\le V_d$.
--
--   The proposition says that a value-maximizing bank must hold enough nondeposit debt that its own default boundary reaches the regulatory one; in particular a bank financed only by deposits and equity is not optimal.
--
--   Differences from the source:
--   - reading: the paper's model under a geometric Brownian motion, with the total bank value given in the Online Appendix (not held) → the closed-form state-price model, with F = D + B + E from (15)–(17) without restructuring; reason: the Online Appendix is not part of the source; the reconstruction matches the §2 description and reproduces Table 2
--   - reading: the minimum requirement printed as "V ≥ V_l = D/(1−β)" (p.6) → V ≥ max{V_b, V_d}; reason: D/(1−β) is V_b, while V_l = max{V_b, V_d} by the definition at the end of §2.2 (p.6), so the printed equation holds only when V_b ≥ V_d, and the requirement is read with the definition
--   - encoding: liability structures with V ≥ V_l → feasible structures 0 ≤ D < (1 − β)V, C_B ≥ 0, V_d ≤ V; reason: D = (1 − β)V is excluded because (2) is undefined there
--   - encoding: "increasing nondeposit debt" → a larger coupon C_B' > C_B at the same D, with a strictly larger debt value B; reason: the coupon is the choice variable and B is determined by it (p.4); deposits are held fixed, as the sentence changes only the nondeposit debt
--   - generalization: 0 ≤ ω < 1 (p.6 text) → 0 ≤ ω ≤ 1 (Table 1); reason: the Lean statement covers ω = 1 as well and specializes to the p.6 range
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, Proposition 1, p.6

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam
import Definitions.Def_BankLiability_Model

namespace BankLiability

/-- **Proposition 1: a liability structure with V_d < V_b is suboptimal.**
Sundaresan–Wang, *Strategic Bank Liability Structure Under Capital Requirements*, Management
Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, Proposition 1, p.6: "A bank can
increase its value by increasing nondeposit debt if the current nondeposit debt ratio is so low
such that the endogenous default boundary is lower than the regulatory total capital boundary.
That is, the liability structure with V_d < V_b is suboptimal."

For every asset value `V > 0`:
1. if `(D, C_B)` is feasible and `V_d < V_b`, there is a larger coupon `C_B' > C_B` such that
   `(D, C_B')` is feasible, has a strictly larger nondeposit debt value and a strictly larger
   total bank value;
2. consequently every strategic structure has `V_b ≤ V_d`.

**Formalization Note.** The model is the closed-form state-price model of
`Definitions.Def_BankLiability_Model`; the parameters range over Table 1 (`Params`). No
regularity assumption is made: the paper introduces (4) only after Proposition 1. -/
theorem proposition_1 (P : Params) (V : ℝ) (hV : 0 < V) :
    (∀ D CB : ℝ, Feasible P V D CB → defaultBoundary P V D CB < regBoundary P D →
      ∃ CB' : ℝ, CB < CB' ∧ Feasible P V D CB' ∧
        debtValue P V D CB < debtValue P V D CB' ∧
        totalValue P V D CB < totalValue P V D CB') ∧
    (∀ D CB : ℝ, IsStrategic P V D CB → regBoundary P D ≤ defaultBoundary P V D CB) := by sorry

end BankLiability
