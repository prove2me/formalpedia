-- Prove2me | Theorems.Thm_AvramDividend_Classical_linearDividendStrategy_continuousStieltjes_counterexample
-- name    : AvramDividend.Classical.linearDividendStrategy_continuousStieltjes_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:31:09.022887+00:00
-- url     : https://prove2.me/theorems/f7399cdb-f3e4-436a-8c65-dc872e301f9b
-- title:
--   Linear continuous dividend strategy has no right jumps but positive Stieltjes mass
-- statement:
--   On the one-point measurable probability space with the full filtration, the deterministic cumulative dividend strategy D(t)=t is nondecreasing, left-continuous and adapted with D(0)=0. Every time has right limit D(t+)=D(t), so its right-jump set is empty. Nevertheless the corresponding Lebesgue–Stieltjes measure assigns mass 1 to the half-open interval [0,1). This is a concrete counterexample to the claim that every admissible cumulative dividend path has a purely atomic Stieltjes measure. The separate existence of a continuous component matters for stochastic dividend verification.
-- source:
--   Definitions.Def_AvramDividend_Classical_DividendStrategy, definition IsDividendStrategy and dividendMeasure; counterexample D(t)=t to AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
local instance : MeasurableSpace Unit := ⊤

theorem AvramDividend.Classical.linearDividendStrategy_continuousStieltjes_counterexample :
    ∃ (𝓕 : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit)),
      IsDividendStrategy 𝓕 (fun t (_ : Unit) => (t : ℝ)) ∧
      (∀ t : ℝ≥0, rightLimit (fun s (_ : Unit) => (s : ℝ)) t () = (t : ℝ)) ∧
      dividendMeasure (fun t (_ : Unit) => (t : ℝ)) ()
        (Ico (0 : ℝ) 1) = (1 : ENNReal) := by
  sorry
