-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_row_upG_other
-- name    : Formalism.L2.FormalSeriesBounds.subst_row_upG_other
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:34.033507+00:00
-- url     : https://prove2.me/theorems/6876e114-463c-521f-a47e-ffc9b833a9bc
-- title:
--   Formal Series Bounds: subst row up G other
-- statement:
--   The Formal Series Bounds construction uses the subst row up G other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L347-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L347-L355

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem Formalism.L2.FormalSeriesBounds.subst_row_upG_other (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (F : MvPowerSeries (I (1 - g)) C) :
    subst (linS (rowM g e v')) (upG (1 - g) F) =
      rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (subst (linS v') F) := by sorry
