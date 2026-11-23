-- Prove2me | Theorems.Thm_Formalism_FG_WittVectorsCharZero_zlToW_injective
-- name    : Formalism.FG.WittVectorsCharZero.zlToW_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:01.09971+00:00
-- url     : https://prove2.me/theorems/1c96b12b-3609-4bf3-bb8f-0455311b5d3c
-- title:
--   Witt Vectors Char Zero: zl To W injective
-- statement:
--   The Witt Vectors Char Zero construction uses the zl To W injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/WittTeichmullerRoot.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/WittTeichmullerRoot.lean#L7-L10

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.WittVectorsCharZero

theorem Formalism.FG.WittVectorsCharZero.zlToW_injective (l : ℕ) [Fact l.Prime] : Function.Injective (zlToW l) := by sorry
