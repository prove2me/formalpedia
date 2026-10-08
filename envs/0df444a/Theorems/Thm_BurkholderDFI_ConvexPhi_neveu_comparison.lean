-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_neveu_comparison
-- name    : BurkholderDFI.ConvexPhi.neveu_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:12.087548+00:00
-- url     : https://prove2.me/theorems/0ea26dd6-a763-429a-b437-1fdfbe774de4
-- title:
--   §16 — Neveu's convex comparison principle (cited)
-- statement:
--   Let $W,Z$ be nonnegative measurable random variables satisfying
--   $$
--   \int_{\{W>\lambda\}}(W-\lambda)\,dP
--   \le\int_{\{W>\lambda\}}Z\,dP
--   \qquad(\lambda>0).
--   $$
--   For every convex moderate-growth function $\Phi$, there is a constant $C>0$, depending only on its doubling constant, such that
--   $$
--   E\Phi(W)\le C E\Phi(Z).
--   $$
--   This cited comparison converts Neveu's pair inequality into the convexity lemma.
--
--   **Formalization Note** The constant is chosen before the probability space, variables, and $\Phi$. The variables and expectations may be infinite.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §16, proof of Lemma 16.1, p. 34 (Neveu [33], [30])

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- §16, p. 34: Neveu's cited comparison principle. -/
theorem neveu_comparison (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W Z : Ω → ℝ≥0∞), Measurable W → Measurable Z →
        (∀ l : ℝ, 0 < l →
          (∫⁻ ω in {ω | ENNReal.ofReal l < W ω},
            (W ω - ENNReal.ofReal l) ∂P) ≤
          (∫⁻ ω in {ω | ENNReal.ofReal l < W ω}, Z ω ∂P)) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c → BurkholderDFI.SquareFnLp.IsConvexPhi Φ →
          (∫⁻ ω, Φ (W ω) ∂P) ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (Z ω) ∂P := by sorry
end BurkholderDFI.ConvexPhi
