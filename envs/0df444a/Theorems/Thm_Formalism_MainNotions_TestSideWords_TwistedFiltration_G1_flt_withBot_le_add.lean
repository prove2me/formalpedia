-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_withBot_le_add
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withBot_le_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:24.73261+00:00
-- url     : https://prove2.me/theorems/697841d1-dbf4-4a16-8b94-103ba2e9b024
-- title:
--   G1: flt with Bot le add
-- statement:
--   The G1 construction uses the flt with Bot le add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L300-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L300-L323

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withBot_le_add {a b c : WithBot ℤ}
    (h : ∀ t u : ℤ, a ≤ (t : WithBot ℤ) → b ≤ (u : WithBot ℤ) → c ≤ ((t + u : ℤ) : WithBot ℤ)) : c ≤ a + b := by sorry
