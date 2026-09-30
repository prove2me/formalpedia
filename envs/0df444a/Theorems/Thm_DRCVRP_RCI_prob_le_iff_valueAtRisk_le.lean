-- Prove2me | Theorems.Thm_DRCVRP_RCI_prob_le_iff_valueAtRisk_le
-- name    : DRCVRP.RCI.prob_le_iff_valueAtRisk_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:20:45.885924+00:00
-- url     : https://prove2.me/theorems/d45212c5-86c5-49c2-9760-f7c15be99016
-- title:
--   Chance constraint $\iff$ value-at-risk bound
-- statement:
--   Let $\mathbb Q$ be a probability distribution on $\mathbb R^n$, let $\tilde X$ be a real-valued measurable function of the demand vector, and let $\epsilon\in(0,1)$. Write $\mathbb Q\text{-VaR}_{1-\epsilon}[\tilde X]=\inf\{x\in\mathbb R:\mathbb Q[\tilde X\le x]\ge 1-\epsilon\}$ for the $(1-\epsilon)$-quantile of $\tilde X$. Then for every threshold $\tau\in\mathbb R$,
--   $$
--   \mathbb Q\big[\tilde X\le\tau\big]\ge 1-\epsilon\iff \mathbb Q\text{-VaR}_{1-\epsilon}\big[\tilde X\big]\le\tau .
--   $$
--
--   This equivalence turns an individual chance constraint into a deterministic bound on a quantile, and underlies the definition of the demand estimator.
--
--   **Formalization Note** The probability bound is written `ENNReal.ofReal (1 - ε) ≤ P {q | X q ≤ τ}`; VaR is `MultistageStochastic.valueAtRisk P X (1 - ε)`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 720 (unlabelled display after the definition of VaR)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.RCI

/-- §3, p. 720: for a random variable `X̃` governed by a probability distribution `ℚ` and
`ε ∈ (0,1)`, `ℚ[X̃ ≤ τ] ≥ 1 - ε ⟺ ℚ-VaR_{1-ε}[X̃] ≤ τ` for every threshold `τ`. -/
theorem prob_le_iff_valueAtRisk_le {n : ℕ} (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (X : (Fin n → ℝ) → ℝ) (hX : Measurable X) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (τ : ℝ) :
    ENNReal.ofReal (1 - ε) ≤ P {q | X q ≤ τ} ↔
      MultistageStochastic.valueAtRisk P X (1 - ε) ≤ τ := by sorry

end DRCVRP.RCI
