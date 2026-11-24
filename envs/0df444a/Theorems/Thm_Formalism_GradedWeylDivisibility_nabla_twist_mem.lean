-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nabla_twist_mem
-- name    : Formalism.GradedWeylDivisibility.nabla_twist_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:00.350197+00:00
-- url     : https://prove2.me/theorems/830cd271-d593-41ad-9b63-46428c2b17bf
-- title:
--   Graded Weyl Divisibility: nabla twist mem
-- statement:
--   The Graded Weyl Divisibility construction uses the nabla twist mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLTwMem.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLTwMem.lean#L7-L25

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLTwMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.nabla_twist_mem : NablaLTwMem := by sorry
