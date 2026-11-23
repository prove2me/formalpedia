-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowActDiagWeight
-- name    : Formalism.GradedWeylDivisibility.rowActDiagWeight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:08.604736+00:00
-- url     : https://prove2.me/theorems/e64876da-28f9-4c3c-8063-a60ae6ed5dfd
-- title:
--   Graded Weyl Divisibility: row Act Diag Weight
-- statement:
--   The Graded Weyl Divisibility construction uses the row Act Diag Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalD.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalD.lean#L19-L19

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSIdxFinite
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSBasis
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowActDiagWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowActMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLLe
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLBasis
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLKBasis
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLDiag
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLTwist
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLTwMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BlockActTensor
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.rowActDiagWeight : RowActDiagWeight := by sorry
