-- Prove2me | Theorems.Thm_AgriSubsidy_Budget_proposition_8
-- name    : AgriSubsidy.Budget.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:44.042546+00:00
-- url     : https://prove2.me/theorems/e3069083-5e89-42aa-9493-e12978b826c2
-- title:
--   Proposition 8, p. 19 — optimal planting, harvesting, and combined designs
-- statement:
--   Suppose the target $\bar Q$ exceeds the all-active no-subsidy output. Assume each of the three designs in Proposition 8 has an equilibrium in which every farmer produces. Then the design $s_P^P$ minimizes the government's feasible planting-only budgets, $s_H^H$ minimizes its feasible harvesting-only budgets, and $(s_P^C,s_H^C)$ minimizes its feasible combined budgets:
--
--   $$s_P^P=\frac{\beta(N+1)\bar Q/N-\bar a(0,0)}{\bar z},\quad s_H^H=\frac{\beta(N+1)\bar Q}{N}-\bar a(0,0),\quad (s_P^C,s_H^C)=\left(\frac{c_P}{2},\frac{\beta(N+1)\bar Q}{N}-\bar a(0,0)-\frac{c_P\bar z}{2}\right).$$
--
--   This result identifies actual minimizers of the three feasible budget sets, not merely profiles meeting the output target.
--
--   **Formalization Note** Proposition 8's proof fixes the active set. The theorem makes that condition explicit by requiring an all-positive equilibrium at each design and by optimizing only over all-active feasible profiles. The theorem asserts leastness, not uniqueness.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), p. 19, Proposition 8; proof, Online Appendix pp. 9–10

import Mathlib
import Definitions.Def_AgriSubsidy_Budget_Setting

namespace AgriSubsidy.Budget

/-- Proposition 8(i)–(iii) with the paper's active set fixed to all farmers. -/
theorem proposition_8 {N : ℕ} (hN : 0 < N) (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ)
    (hS : Standing P z) (Qbar : ℝ)
    (hQ : QC P z 0 0 < Qbar)
    (qP qH qC : Fin N → ℝ)
    (hEqP : IsEquilibrium P z (AgriSubsidy.Combined.combined z (sPP P z Qbar) 0) qP)
    (hPosP : ∀ j, 0 < qP j)
    (hEqH : IsEquilibrium P z (AgriSubsidy.Combined.combined z 0 (sHH P z Qbar)) qH)
    (hPosH : ∀ j, 0 < qH j)
    (hEqC : IsEquilibrium P z (AgriSubsidy.Combined.combined z (sCP P) (sCH P z Qbar)) qC)
    (hPosC : ∀ j, 0 < qC j) :
    IsLeast (feasibleBudgets P z (plantingProg z) Qbar)
      (∑ j, AgriSubsidy.Combined.combined z (sPP P z Qbar) 0 j * qP j) ∧
    IsLeast (feasibleBudgets P z (harvestingProg z) Qbar)
      (∑ j, AgriSubsidy.Combined.combined z 0 (sHH P z Qbar) j * qH j) ∧
    IsLeast (feasibleBudgets P z (combinedProg z) Qbar)
      (∑ j, AgriSubsidy.Combined.combined z (sCP P) (sCH P z Qbar) j * qC j) := by sorry

end AgriSubsidy.Budget
