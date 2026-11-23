-- Prove2me | Theorems.Thm_Formalism_FG_WittVectorsCharZero_neZero_cast
-- name    : Formalism.FG.WittVectorsCharZero.neZero_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:13.334183+00:00
-- url     : https://prove2.me/theorems/a740b041-2052-4b29-b9c7-e30011999252
-- title:
--   Witt Vectors Char Zero: ne Zero cast
-- statement:
--   The Witt Vectors Char Zero construction uses the ne Zero cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/WittTeichmullerRoot.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/WittTeichmullerRoot.lean#L12-L17

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

theorem Formalism.FG.WittVectorsCharZero.neZero_cast (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : 1 ≤ d) :
    NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := by sorry
