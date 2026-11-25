-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fock_space_highest_weight
-- name    : Formalism.GradedWeylDivisibility.fock_space_highest_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:05.84711+00:00
-- url     : https://prove2.me/theorems/3d4a8782-7cd8-4009-94da-8c2d67d96e9e
-- title:
--   Graded Weyl Divisibility: fock space highest weight
-- statement:
--   The Graded Weyl Divisibility construction uses the fock space highest weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQHW.lean#L24-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQHW.lean#L24-L66

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
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

theorem Formalism.GradedWeylDivisibility.fock_space_highest_weight : FockQHW := by sorry
