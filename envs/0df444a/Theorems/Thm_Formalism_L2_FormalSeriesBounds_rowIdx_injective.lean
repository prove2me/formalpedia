-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowIdx_injective
-- name    : Formalism.L2.FormalSeriesBounds.rowIdx_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:05.090893+00:00
-- url     : https://prove2.me/theorems/574838b3-b6dc-44aa-8a15-5c08a3b3232f
-- title:
--   Formal Series Bounds: row Idx injective
-- statement:
--   The Formal Series Bounds construction uses the row Idx injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L612-L626
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L612-L626

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

theorem Formalism.L2.FormalSeriesBounds.rowIdx_injective (g : Fin 2) : Function.Injective (rowIdx g : WV I → I g ⊕ I (1 - g)) := by sorry
