-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_linS_rowM_other
-- name    : Formalism.L2.FormalSeriesBounds.linS_rowM_other
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:11.464101+00:00
-- url     : https://prove2.me/theorems/8d428068-64d2-4db2-8989-11119e7ad4f6
-- title:
--   Formal Series Bounds: lin S row M other
-- statement:
--   The Formal Series Bounds construction uses the lin S row M other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L315-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L315-L327

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

theorem Formalism.L2.FormalSeriesBounds.linS_rowM_other (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (x : I (1 - g)) :
    linS (rowM g e v') (⟨1 - g, x⟩ : WV I) =
      rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (linS v' x) := by sorry
