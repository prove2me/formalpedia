-- Prove2me | Theorems.Thm_BilateralProfitRegular_refine_phase_budgets
-- name    : BilateralProfitRegular.refine_phase_budgets
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-18T16:02:43.842644+00:00
-- url     : https://prove2.me/theorems/0bc99e53-e622-4062-9ec2-4e6c604a4a6f
-- title:
--   Refinement run lengths and probability budgets
-- statement:
--   Choose the run-size constant after the positive bounds on observation size and expected regret. For each admissible phase, the prescribed length makes the expected regret fit the Markov budget. The prescribed number of copies makes both the all-copy failure probability and the observation-deviation union bound at most one half of the reciprocal horizon. Admissibility uses the previous run length except in phase zero.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 6.6, pp. 44–46.

import Mathlib
import Definitions.Def_BilateralProfitRegular_Refinement

namespace BilateralProfitRegular


theorem refine_phase_budgets (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (T j : ℕ), 0 < T →
      (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) → ∀ δ : ℝ, 0 < δ →
      let n := phaseLen C₀ T j
      let M := numCopies C₀ T
      let ε := acc δ j
      0 < n ∧ 0 < ε ∧
      C₂ / δ * Real.sqrt n * Real.log (2 * (n : ℝ)) ^ 2 ≤ (n : ℝ) * ε / (800 * δ ^ 2) ∧
      (1 / 4 : ℝ) ^ M ≤ 1 / (2 * (T : ℝ)) ∧
      (M : ℝ) * (2 * Real.exp (-(2 * (n : ℝ) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2))) ≤
        1 / (2 * (T : ℝ)) := by sorry

end BilateralProfitRegular
