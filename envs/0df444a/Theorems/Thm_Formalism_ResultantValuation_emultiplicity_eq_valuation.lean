-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_emultiplicity_eq_valuation
-- name    : Formalism.ResultantValuation.emultiplicity_eq_valuation
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:17.211812+00:00
-- url     : https://prove2.me/theorems/d8060e22-15db-41ef-ae08-d4e2a43fcb15
-- title:
--   Resultant Valuation: emultiplicity eq valuation
-- statement:
--   The Resultant Valuation construction uses the emultiplicity eq valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Window.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Window.lean#L18-L23

import Mathlib
import Definitions.Def_Formalism_ResultantValuation_WindowValuation
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.ResultantValuation
variable {l : ℕ} [Fact l.Prime]

theorem Formalism.ResultantValuation.emultiplicity_eq_valuation {x : ℤ_[l]} (hx : x ≠ 0) :
    emultiplicity (l : ℤ_[l]) x = (x.valuation : ℕ∞) := by sorry
