-- Prove2me | Theorems.Thm_AgriSubsidy_Budget_prop10_proof_single_gap
-- name    : AgriSubsidy.Budget.prop10_proof_single_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:29.080961+00:00
-- url     : https://prove2.me/theorems/2721b980-f9d3-431e-881c-6ed3fd9aa2e3
-- title:
--   Proof of Proposition 10, OA p. 13 — the harvesting-minus-planting budget gap
-- statement:
--   Let $s_P^P$ and $s_H^H$ be the two single-subsidy designs of Proposition 8, and take all-positive Cournot equilibria at those designs. The difference between the harvesting-only and planting-only government budgets is
--
--   $$b^C(0,s_H^H)-b^C(s_P^P,0)=\frac{Nv_z}{\beta}(c_P-s_P^P)s_P^P.$$
--
--   This exact identity determines which single subsidy is cheaper on either side of the threshold $Q^C(c_P,0)$.
--
--   **Formalization Note** The budgets are sums of payments to equilibrium outputs. The source uses $n$ for the active-farmer count; here all $N$ farmers are active.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), Online Appendix p. 13, Proof of Proposition 10, first budget-difference display

import Mathlib
import Definitions.Def_AgriSubsidy_Budget_Setting

namespace AgriSubsidy.Budget

/-- The first budget-difference display in the proof of Proposition 10. -/
theorem prop10_proof_single_gap {N : ℕ} (hN : 0 < N) (P : AgriSubsidy.Combined.Params)
    (z : Fin N → ℝ) (hS : Standing P z) (Qbar : ℝ)
    (hQ : QC P z 0 0 < Qbar) (qP qH : Fin N → ℝ)
    (hEqP : IsEquilibrium P z (AgriSubsidy.Combined.combined z (sPP P z Qbar) 0) qP)
    (hPosP : ∀ j, 0 < qP j)
    (hEqH : IsEquilibrium P z (AgriSubsidy.Combined.combined z 0 (sHH P z Qbar)) qH)
    (hPosH : ∀ j, 0 < qH j) :
    (∑ j, AgriSubsidy.Combined.combined z 0 (sHH P z Qbar) j * qH j) -
      (∑ j, AgriSubsidy.Combined.combined z (sPP P z Qbar) 0 j * qP j) =
      (N : ℝ) * vz z / P.β * (P.cP - sPP P z Qbar) * sPP P z Qbar := by sorry

end AgriSubsidy.Budget
