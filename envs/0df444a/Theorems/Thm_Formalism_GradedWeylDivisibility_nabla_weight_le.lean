-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nabla_weight_le
-- name    : Formalism.GradedWeylDivisibility.nabla_weight_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:00.007256+00:00
-- url     : https://prove2.me/theorems/b2f5bf71-22bf-4b34-b14d-a67b5f93aba5
-- title:
--   Graded Weyl Divisibility: nabla weight le
-- statement:
--   The Graded Weyl Divisibility construction uses the nabla weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLLe.lean#L11-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLLe.lean#L11-L114

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowActMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.nabla_weight_le : NablaLLe := by sorry
