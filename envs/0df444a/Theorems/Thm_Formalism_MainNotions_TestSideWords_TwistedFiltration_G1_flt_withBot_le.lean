-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_withBot_le
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withBot_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:38.480819+00:00
-- url     : https://prove2.me/theorems/251650be-55e7-4e4a-87d7-a8a91b9dffd2
-- title:
--   G1: flt with Bot le
-- statement:
--   The G1 construction uses the flt with Bot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L258-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L258-L270

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withBot_le {a b : WithBot ℤ} {N : ℤ}
    (h : ∀ M : ℤ, b ≤ (M : WithBot ℤ) → a ≤ ((M + N : ℤ) : WithBot ℤ)) : a ≤ b + (N : WithBot ℤ) := by sorry
