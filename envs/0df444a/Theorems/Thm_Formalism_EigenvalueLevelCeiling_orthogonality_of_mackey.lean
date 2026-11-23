-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_orthogonality_of_mackey
-- name    : Formalism.EigenvalueLevelCeiling.orthogonality_of_mackey
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:48.257188+00:00
-- url     : https://prove2.me/theorems/781e0202-fb76-41f9-9003-7a449803dd1d
-- title:
--   Eigenvalue Level Ceiling: orthogonality of mackey
-- statement:
--   The Eigenvalue Level Ceiling construction uses the orthogonality of mackey property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/OrthogonalityOfMackey.lean#L8-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/OrthogonalityOfMackey.lean#L8-L48

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling

theorem Formalism.EigenvalueLevelCeiling.orthogonality_of_mackey : OrthOfMackey := by sorry
