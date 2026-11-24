-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxMono
-- name    : Formalism.EigenvalueLevelCeiling.idxMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:55.849288+00:00
-- url     : https://prove2.me/theorems/f746fa0e-ad1a-4759-9d83-319ad09f1dd7
-- title:
--   Eigenvalue Level Ceiling: idx Mono
-- statement:
--   The Eigenvalue Level Ceiling construction uses the idx Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicIsMackey.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicIsMackey.lean#L17-L17

import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxFull
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxPsiGood
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnExport
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnLocal
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling

theorem Formalism.EigenvalueLevelCeiling.idxMono : IdxMono := by sorry
