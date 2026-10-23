-- Prove2me | Theorems.Thm_AgriSubsidy_Budget_proposition_10
-- name    : AgriSubsidy.Budget.proposition_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:23.31604+00:00
-- url     : https://prove2.me/theorems/5d06fbf2-9e57-4da6-8262-6fbb2d93355e
-- title:
--   Proposition 10, p. 22 — budget ordering of the four subsidy programs
-- statement:
--   Let the target $\bar Q$ exceed the no-subsidy output, and suppose every farmer produces at the planting-only, harvesting-only, and combined designs of Proposition 8. Write $B_C,B_S,B_P,B_H$ for the least feasible budgets under the combined, selective, planting-only, and harvesting-only programs, respectively. Then
--
--   $$\bar Q\le Q^C(c_P,0)\ \Longrightarrow\ B_C\le B_S\le B_P\le B_H,$$
--   $$\bar Q>Q^C(c_P,0)\ \Longrightarrow\ B_C\le B_S\le B_H\le B_P.$$
--
--   Moreover, if $v_z=0$, all four optimal budgets are equal. The result compares the government's least spending required to reach the same market output under four subsidy formats.
--
--   **Formalization Note** The paper's phrase “all farmers produce” is read as restricting each feasible program to all-active Cournot equilibria and requiring the three closed-form designs to be all-active. The strict target condition is the standing assumption of §5. Each feasible set is nonempty under these hypotheses; the selective program contains a single-subsidy design. The lower bound from the proof of Proposition 10 prevents its real infimum from being a junk value. The threshold is equation (5) evaluated at $(c_P,0)$, with $n=N$.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), p. 22, Proposition 10; proof, Online Appendix p. 13

import Mathlib
import Definitions.Def_AgriSubsidy_Budget_Setting

namespace AgriSubsidy.Budget

/-- Proposition 10, with all four government programs restricted to all-active equilibria. -/
theorem proposition_10 {N : ℕ} (hN : 0 < N) (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ)
    (hS : Standing P z) (Qbar : ℝ)
    (hQ : QC P z 0 0 < Qbar)
    (hP : AllActiveAt P z (AgriSubsidy.Combined.combined z (sPP P z Qbar) 0))
    (hH : AllActiveAt P z (AgriSubsidy.Combined.combined z 0 (sHH P z Qbar)))
    (hC : AllActiveAt P z (AgriSubsidy.Combined.combined z (sCP P) (sCH P z Qbar))) :
    (Qbar ≤ QC P z P.cP 0 →
      optBudget P z (combinedProg z) Qbar ≤ optBudget P z (selectiveProg z) Qbar ∧
      optBudget P z (selectiveProg z) Qbar ≤ optBudget P z (plantingProg z) Qbar ∧
      optBudget P z (plantingProg z) Qbar ≤ optBudget P z (harvestingProg z) Qbar) ∧
    (QC P z P.cP 0 < Qbar →
      optBudget P z (combinedProg z) Qbar ≤ optBudget P z (selectiveProg z) Qbar ∧
      optBudget P z (selectiveProg z) Qbar ≤ optBudget P z (harvestingProg z) Qbar ∧
      optBudget P z (harvestingProg z) Qbar ≤ optBudget P z (plantingProg z) Qbar) ∧
    (vz z = 0 →
      optBudget P z (plantingProg z) Qbar = optBudget P z (harvestingProg z) Qbar ∧
      optBudget P z (harvestingProg z) Qbar = optBudget P z (combinedProg z) Qbar ∧
      optBudget P z (combinedProg z) Qbar = optBudget P z (selectiveProg z) Qbar) := by sorry

end AgriSubsidy.Budget
