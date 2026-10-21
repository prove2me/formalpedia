-- Prove2me | Theorems.Thm_AccountingRules_Threshold_case_2_2_threshold_optimal
-- name    : AccountingRules.Threshold.case_2_2_threshold_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:58.773992+00:00
-- url     : https://prove2.me/theorems/3a9b16a8-cd33-49ee-9f68-734319e5621f
-- title:
--   Appendix A.1, Case 2.2 — the binding threshold solves the binary program
-- statement:
--   In Case 2.2, let $\hat\theta\in(M-B,M)$ solve $\mathbb E_P[\theta\mid\theta\le\hat\theta]=M-B$, and set $m^*(\theta)=1\{\theta>\hat\theta\}$. There is a positive multiplier $\lambda>0$ for which $\hat\theta=M-\lambda B/(1+\lambda)$. The rule $m^*$ satisfies (A.1) and (A.2), and (A.1) binds,
--   $$\int\theta(1-m^*)\,dP=(M-B)\int(1-m^*)\,dP,$$
--   and its objective is at least that of every binary rule satisfying those constraints. This is the binary-program optimality step behind Proposition 2.
--
--   **Formalization Note** The strict lower-support and positive-benefit guards are the corrected Proposition 2 regime. All conditional means have positive denominators.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, p. 10 (PDF 11), Appendix A.1, Case 2.2

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, Case 2.2, p. 10: the binding threshold solves the binary program. -/
theorem case_2_2_threshold_optimal (P : Measure ℝ) (θlo θhi M B t : ℝ)
    (hS : Standing P θlo θhi M B) (hlo : θlo < M - B) (hB : 0 < B)
    (hcond : M - B < condMean P id (Iic M))
    (ht : t ∈ Ioo (M - B) M) (hroot : condMean P id (Iic t) = M - B) :
    let mstar : ℝ → ℝ := (Ioi t).indicator (fun _ => (1 : ℝ))
    ∃ lam : ℝ, 0 < lam ∧ t = M - lam / (1 + lam) * B ∧
      A1 P M B mstar ∧ A2 P M B mstar ∧
        (∫ θ, θ * (1 - mstar θ) ∂P) =
          (M - B) * ∫ θ, (1 - mstar θ) ∂P ∧
        ∀ m : ℝ → ℝ, IsRule m → A1 P M B m → A2 P M B m →
          objective P M m ≤ objective P M mstar := by sorry

end AccountingRules.Threshold
