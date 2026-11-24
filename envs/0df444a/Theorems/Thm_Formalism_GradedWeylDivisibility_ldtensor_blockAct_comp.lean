-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_blockAct_comp
-- name    : Formalism.GradedWeylDivisibility.ldtensor_blockAct_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:03.776273+00:00
-- url     : https://prove2.me/theorems/ac56de1e-4e77-4cc7-a6f7-772a110c7b1a
-- title:
--   Graded Weyl Divisibility: ldtensor block Act comp
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor block Act comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BlockActTensor.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BlockActTensor.lean#L9-L15

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BlockActTensor
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

theorem Formalism.GradedWeylDivisibility.ldtensor_blockAct_comp (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) :
    (blockAct K (n := n) g).comp (blockEmb K (k := k) (n := n) s) =
      (blockEmb K s).comp (rowAct K (g s)) := by sorry
