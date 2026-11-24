-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fock_space_word_adjoint
-- name    : Formalism.GradedWeylDivisibility.fock_space_word_adjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:21.569806+00:00
-- url     : https://prove2.me/theorems/bc2e4157-3d51-4dd5-84d6-13e158cf89f7
-- title:
--   Graded Weyl Divisibility: fock space word adjoint
-- statement:
--   The Graded Weyl Divisibility construction uses the fock space word adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L22-L29

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
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

theorem Formalism.GradedWeylDivisibility.fock_space_word_adjoint : FockQWordAdj := by sorry
