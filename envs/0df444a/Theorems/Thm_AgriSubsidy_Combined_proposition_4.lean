-- Prove2me | Theorems.Thm_AgriSubsidy_Combined_proposition_4
-- name    : AgriSubsidy.Combined.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:34.784518+00:00
-- url     : https://prove2.me/theorems/991e02df-68a9-4244-baa8-2af291dba1ed
-- title:
--   Proposition 4, p. 13 — productivity dispersion orders outputs, increments, and profits
-- statement:
--   Consider two otherwise identical $N$-farmer markets, $A$ and $B$, with input-to-output ratio vectors $z_A\ge^m z_B$. Give both the same combined subsidy $(s_P,s_H)$ and a positive increment $\delta$. Let their equilibria at $(s_P,s_H)$, $(s_P+\delta,s_H)$, and $(s_P,s_H+\delta)$ have every farmer active. Then
--
--   $$q_A\ge^m q_B,\qquad \Delta_{s_P}q_A\ge^m\Delta_{s_P}q_B,\qquad \Delta_{s_H}q_A=^m\Delta_{s_H}q_B,$$
--
--   $$\pi_A\ge_{wm}\pi_B,\qquad \Delta_{s_H}\pi_A\ge^m\Delta_{s_H}\pi_B.$$
--
--   Here each increment is the difference between the equilibrium quantity or profit at the shifted subsidy and at the baseline subsidy. The theorem compares how farmer productivity dispersion carries through to production and to profit under the combined payment.
--
--   **Formalization Note** The same market parameters $\alpha,\beta,c_P,c_H$ and farmer count are shared by the two ratio vectors. The equality $=^m$ asserts majorization in both directions. Positive output at the planting-shifted subsidy is an added assumption needed for the increment formula; positive output at the harvesting-shifted subsidy is also explicit, though implied by the model. The shared standing conditions include $N>0$, ordered positive ratios, and $\alpha,\beta>0$.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), p. 13, Proposition 4

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Setting
import Definitions.Def_AgriSubsidy_Combined_Majorization

namespace AgriSubsidy.Combined

theorem proposition_4 {N : ℕ} (P : Params) (zA zB : Fin N → ℝ)
    (hA : Standing P zA) (hB : Standing P zB) (hz : Majorizes zA zB)
    (sP sH δ : ℝ) (hδ : 0 < δ)
    (qA qAP qAH qB qBP qBH : Fin N → ℝ)
    (eA : IsEquilibrium P zA (combined zA sP sH) qA)
    (eAP : IsEquilibrium P zA (combined zA (sP + δ) sH) qAP)
    (eAH : IsEquilibrium P zA (combined zA sP (sH + δ)) qAH)
    (eB : IsEquilibrium P zB (combined zB sP sH) qB)
    (eBP : IsEquilibrium P zB (combined zB (sP + δ) sH) qBP)
    (eBH : IsEquilibrium P zB (combined zB sP (sH + δ)) qBH)
    (hpos : ∀ j, 0 < qA j ∧ 0 < qAP j ∧ 0 < qAH j ∧
      0 < qB j ∧ 0 < qBP j ∧ 0 < qBH j) :
    Majorizes qA qB ∧
    Majorizes (qAP - qA) (qBP - qB) ∧
    (Majorizes (qAH - qA) (qBH - qB) ∧
      Majorizes (qBH - qB) (qAH - qA)) ∧
    WeakSubMaj
      (fun j => profit P zA (combined zA sP sH) qA j)
      (fun j => profit P zB (combined zB sP sH) qB j) ∧
    Majorizes
      (fun j => profit P zA (combined zA sP (sH + δ)) qAH j -
        profit P zA (combined zA sP sH) qA j)
      (fun j => profit P zB (combined zB sP (sH + δ)) qBH j -
        profit P zB (combined zB sP sH) qB j) := by sorry

end AgriSubsidy.Combined
