-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nablaLDiag
-- name    : Formalism.GradedWeylDivisibility.nablaLDiag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:09.423807+00:00
-- url     : https://prove2.me/theorems/ad601172-a601-4adc-9443-a794d46d43d8
-- title:
--   Graded Weyl Divisibility: nabla LDiag
-- statement:
--   The Graded Weyl Divisibility construction uses the nabla LDiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalD.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalD.lean#L24-L24

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

theorem Formalism.GradedWeylDivisibility.nablaLDiag : NablaLDiag := by sorry
