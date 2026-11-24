-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_blockAct_blockEmb
-- name    : Formalism.GradedWeylDivisibility.ldtensor_blockAct_blockEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:31.806446+00:00
-- url     : https://prove2.me/theorems/bd98b739-8918-406e-9447-35d9126b3110
-- title:
--   Graded Weyl Divisibility: ldtensor block Act block Emb
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor block Act block Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BlockActTensor.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BlockActTensor.lean#L17-L20

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

theorem Formalism.GradedWeylDivisibility.ldtensor_blockAct_blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) := by sorry
