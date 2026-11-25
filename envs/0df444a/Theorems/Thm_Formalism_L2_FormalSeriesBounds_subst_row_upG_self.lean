-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_row_upG_self
-- name    : Formalism.L2.FormalSeriesBounds.subst_row_upG_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:59.35689+00:00
-- url     : https://prove2.me/theorems/81c4a3d5-93ba-4a70-9d19-35b8c2becfdb
-- title:
--   Formal Series Bounds: subst row up G self
-- statement:
--   The Formal Series Bounds construction uses the subst row up G self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L337-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L337-L345

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

theorem Formalism.L2.FormalSeriesBounds.subst_row_upG_self (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (F : MvPowerSeries (I g) C) :
    subst (linS (rowM g e v')) (upG g F) =
      rename (Function.Embedding.inl : ι ↪ ι ⊕ ι') (subst (linS e) F) := by sorry
