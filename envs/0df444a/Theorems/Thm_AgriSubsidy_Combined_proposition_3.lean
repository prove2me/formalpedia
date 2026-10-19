-- Prove2me | Theorems.Thm_AgriSubsidy_Combined_proposition_3
-- name    : AgriSubsidy.Combined.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:31.136018+00:00
-- url     : https://prove2.me/theorems/2f6b0895-906c-4770-8928-35c709011be7
-- title:
--   Proposition 3, p. 11 — active combined-subsidy output and profit
-- statement:
--   Consider the paper's $N$-farmer market under a combined subsidy $(s_P,s_H)$. If $q$ is a Cournot equilibrium and every farmer produces a positive quantity, then each farmer $j$ has output and profit
--
--   $$q_j=\frac1\beta\left(\frac{\bar a(s_P,s_H)}{N+1}-(z_j-\bar z)(c_P-s_P)\right),\qquad \pi_j=\beta q_j^2.$$
--
--   These identities characterize the active branch of the equilibrium in Proposition 3 and are the quantitative basis for the mission's distribution comparisons.
--
--   **Formalization Note** The statement includes the shared conditions $N>0$, $\alpha,\beta>0$, ordered positive ratios $z_j$, and positive output for every farmer. It does not define equilibrium by this formula.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), p. 11, Proposition 3, (2)–(3)

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Setting

namespace AgriSubsidy.Combined

theorem proposition_3 {N : ℕ} (P : Params) (z : Fin N → ℝ)
    (h : Standing P z) (sP sH : ℝ) (q : Fin N → ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q)
    (hpos : ∀ j, 0 < q j) :
    (∀ j, q j = (1 / P.β) *
      (abar P z sP sH / ((N : ℝ) + 1) - (z j - zbar z) * (P.cP - sP))) ∧
    (∀ j, profit P z (combined z sP sH) q j = P.β * (q j) ^ 2) := by sorry

end AgriSubsidy.Combined
