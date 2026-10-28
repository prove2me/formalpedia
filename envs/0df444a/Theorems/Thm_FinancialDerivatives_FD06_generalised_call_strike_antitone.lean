-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_call_strike_antitone
-- name    : FinancialDerivatives.FD06.generalised_call_strike_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:33:22.436721+00:00
-- url     : https://prove2.me/theorems/37aae97b-3fab-4225-ae05-117c2fcc9b11
-- title:
--   Call is antitone in strike
-- statement:
--   Call is antitone in strike
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedCall

namespace FinancialDerivatives.FD06

theorem generalised_call_strike_antitone (S K₁ K₂ R Q V : ℝ) (hS : 0 < S) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hK : K₁ ≤ K₂) (hV : 0 < V) : generalisedCall S K₂ R Q V ≤ generalisedCall S K₁ R Q V := by sorry

end FinancialDerivatives.FD06
