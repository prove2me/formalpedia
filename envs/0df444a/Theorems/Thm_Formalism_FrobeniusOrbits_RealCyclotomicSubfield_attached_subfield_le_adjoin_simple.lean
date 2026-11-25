-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_attached_subfield_le_adjoin_simple
-- name    : Formalism.FrobeniusOrbits.RealCyclotomicSubfield.attached_subfield_le_adjoin_simple
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:11.84861+00:00
-- url     : https://prove2.me/theorems/571949cd-1a5f-51fa-9c72-67a00b6f52db
-- title:
--   Real Cyclotomic Subfield: attached subfield le adjoin simple
-- statement:
--   The Real Cyclotomic Subfield construction uses the attached subfield le adjoin simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean#L104-L105

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.FrobeniusOrbits.RealCyclotomicSubfield.attached_subfield_le_adjoin_simple (ζ : L) : F1 ζ ≤ ℚ⟮ζ⟯ := by sorry
