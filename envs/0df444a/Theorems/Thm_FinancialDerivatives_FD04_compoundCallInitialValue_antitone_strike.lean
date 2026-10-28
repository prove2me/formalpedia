-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_compoundCallInitialValue_antitone_strike
-- name    : FinancialDerivatives.FD04.compoundCallInitialValue_antitone_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:52:58.847981+00:00
-- url     : https://prove2.me/theorems/c4f33941-681a-4e4e-b23c-9df319ae083b
-- title:
--   Compound call premium decreases with compound strike
-- statement:
--   Raising the compound strike from L₁ to L₂ weakly decreases its inception premium while holding the underlying call and maturities fixed.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_compoundCallInitialValue

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem compoundCallInitialValue_antitone_strike
    (m : BinomialMarket) (K L₁ L₂ : ℝ)
    (exerciseSteps postExerciseSteps : ℕ) (h : L₁ ≤ L₂) :
    compoundCallInitialValue m K L₂ exerciseSteps postExerciseSteps ≤
      compoundCallInitialValue m K L₁ exerciseSteps postExerciseSteps := by sorry

end FinancialDerivatives.FD04
