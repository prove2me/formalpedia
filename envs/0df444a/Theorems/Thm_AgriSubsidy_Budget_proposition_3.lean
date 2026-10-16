-- Prove2me | Theorems.Thm_AgriSubsidy_Budget_proposition_3
-- name    : AgriSubsidy.Budget.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:19.006769+00:00
-- url     : https://prove2.me/theorems/8b2259c7-f711-4fdb-a6b5-433823769a6c
-- title:
--   Proposition 3, p. 11 — all-active combined-subsidy equilibrium and aggregate quantities
-- statement:
--   In the agricultural Cournot market, offer the combined subsidy $(s_P,s_H)$ and let every farmer produce a positive quantity at equilibrium. With $N$ active farmers, the individual output, profit, industry input, market output, and total profit are exactly the quantities in equations (2)–(6). In particular,
--
--   $$q_j^C=\frac1\beta\left(\frac{\bar a(s_P,s_H)}{N+1}-(z_j-\bar z)(c_P-s_P)\right),\qquad Q^C=\frac{N\bar a(s_P,s_H)}{\beta(N+1)}.$$
--
--   These identities connect equilibrium, which is defined through unilateral best responses, to the formulas used in the government's optimization problem.
--
--   **Formalization Note** The paper's active set is all of `Fin N` here. The theorem includes all five displays (2)–(6), with $n=N$; it does not assert the separate comparative statics clauses of Proposition 3.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), p. 11, Proposition 3, (2)–(6)

import Mathlib
import Definitions.Def_AgriSubsidy_Budget_Setting

namespace AgriSubsidy.Budget

/-- Proposition 3, equations (2)–(6), in the all-active regime. -/
theorem proposition_3 {N : ℕ} (hN : 0 < N) (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ)
    (hS : Standing P z) (sP sH : ℝ) (q : Fin N → ℝ)
    (hEq : IsEquilibrium P z (AgriSubsidy.Combined.combined z sP sH) q)
    (hPos : ∀ j, 0 < q j) :
    (∀ j, q j = (1 / P.β) *
      (AgriSubsidy.Combined.abar P z sP sH / ((N : ℝ) + 1) -
        (z j - AgriSubsidy.Combined.zbar z) * (P.cP - sP))) ∧
    (∀ j, profit P z (AgriSubsidy.Combined.combined z sP sH) q j = P.β * (q j) ^ 2) ∧
    (∑ j, z j * q j) =
      (N : ℝ) / (P.β * ((N : ℝ) + 1)) *
        (AgriSubsidy.Combined.zbar z * AgriSubsidy.Combined.abar P z sP sH - ((N : ℝ) + 1) * vz z * (P.cP - sP)) ∧
    (∑ j, q j) = QC P z sP sH ∧
    (∑ j, profit P z (AgriSubsidy.Combined.combined z sP sH) q j) =
      (N : ℝ) / (P.β * (((N : ℝ) + 1) ^ 2)) *
        ((AgriSubsidy.Combined.abar P z sP sH) ^ 2 + (((N : ℝ) + 1) ^ 2) * vz z * (P.cP - sP) ^ 2) := by sorry

end AgriSubsidy.Budget
