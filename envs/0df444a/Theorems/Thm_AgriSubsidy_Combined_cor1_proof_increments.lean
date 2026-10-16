-- Prove2me | Theorems.Thm_AgriSubsidy_Combined_cor1_proof_increments
-- name    : AgriSubsidy.Combined.cor1_proof_increments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:29.130243+00:00
-- url     : https://prove2.me/theorems/79bce7d1-9c9b-45a9-b83a-b803c1103b10
-- title:
--   Proof of Corollary 1, Online Appendix p. 4 — subsidy increments
-- statement:
--   Fix a market and a subsidy increase $\delta>0$. Suppose the equilibria at $(s_P,s_H)$, $(s_P+\delta,s_H)$, $(s_P,s_H+\delta)$, and $(s_P,s_H+\delta/2)$ have every farmer active. The farmer-level changes obey
--
--   $$\Delta_{s_P}q_j=\frac\delta\beta\left(z_j-\frac{N}{N+1}\bar z\right),\qquad \Delta_{s_H}q_j=\frac\delta{\beta(N+1)},\qquad \Delta_{s_H}\pi_j=\frac{2\delta}{N+1}q_j(s_P,s_H+\delta/2).$$
--
--   These identities describe the output and profit changes used in Proposition 4, with each change computed from the relevant equilibria.
--
--   **Formalization Note** All four equilibria are explicit best-response profiles, not formula-defined vectors. Activity at the planting-shifted subsidy is an added condition needed to retain the same active set. Activity at the harvesting-shifted and midpoint subsidies is stated explicitly; the paper's model implies it from baseline activity, but no uniqueness theorem is assumed here.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), Online Appendix p. 4, Proof of Corollary 1, first and final displayed equations

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Setting

namespace AgriSubsidy.Combined

theorem cor1_proof_increments {N : ℕ} (P : Params) (z : Fin N → ℝ)
    (h : Standing P z) (sP sH δ : ℝ) (hδ : 0 < δ)
    (q qP qH qMid : Fin N → ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q)
    (eqP : IsEquilibrium P z (combined z (sP + δ) sH) qP)
    (eqH : IsEquilibrium P z (combined z sP (sH + δ)) qH)
    (eqMid : IsEquilibrium P z (combined z sP (sH + δ / 2)) qMid)
    (hpos : ∀ j, 0 < q j ∧ 0 < qP j ∧ 0 < qH j ∧ 0 < qMid j) :
    (∀ j, qP j - q j = (δ / P.β) *
      (z j - ((N : ℝ) / ((N : ℝ) + 1)) * zbar z)) ∧
    (∀ j, qH j - q j = δ / (P.β * ((N : ℝ) + 1))) ∧
    (∀ j, profit P z (combined z sP (sH + δ)) qH j -
      profit P z (combined z sP sH) q j =
      (2 * δ / ((N : ℝ) + 1)) * qMid j) := by sorry

end AgriSubsidy.Combined
