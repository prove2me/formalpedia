-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_14_4
-- name    : BurkholderDFI.ConvexPhi.eq_14_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:08.659689+00:00
-- url     : https://prove2.me/theorems/3ea54399-f902-47de-a055-ab713d7191c6
-- title:
--   (14.4) — total variation bound for the large-jump part
-- statement:
--   For Davis's decomposition of a martingale, the large-jump differences satisfy
--   $$
--   \sum_{k\ge1}|b_k|\le
--   \sum_{k\ge1}|z_k|+
--   \sum_{k\ge1}E(|z_k|\mid\mathcal A_{k-1})
--   \quad\text{almost surely}.
--   $$
--   This controls the process $h$ by its large jumps and their predictable projections.
--
--   **Formalization Note** The sums and projections of nonnegative quantities take values in $[0,\infty]$; projections use the extended nonnegative conditional expectation. The real conditional expectation inside $b_k$ is valid because $y_k$ is integrable.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (14.4), p. 33

import Mathlib
import Definitions.Def_BurkholderDFI_ConvexPhi_Davis

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (14.4), p. 33: the large-jump martingale's total variation bound. -/
theorem eq_14_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    ∀ᵐ ω ∂P,
      (∑' k : ℕ, ENNReal.ofReal |davisB ℱ P f (k + 1) ω|) ≤
        (∑' k : ℕ, ENNReal.ofReal |davisZ f (k + 1) ω|) +
        (∑' k : ℕ, condLExp (ℱ k) P
          (fun x => ENNReal.ofReal |davisZ f (k + 1) x|) ω) := by sorry
end BurkholderDFI.ConvexPhi
