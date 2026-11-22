-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_rowMat_conjTranspose
-- name    : Formalism.GradedWeylDivisibility.LFocks_rowMat_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:42.772743+00:00
-- url     : https://prove2.me/theorems/c97bb7f8-e6f8-4cf3-b2b6-63f26bfd23e4
-- title:
--   Graded Weyl Divisibility: LFocks row Mat conj Transpose
-- statement:
--   The Graded Weyl Divisibility construction uses the LFocks row Mat conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockRowAdj.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockRowAdj.lean#L27-L33

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.LFocks_rowMat_conjTranspose {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    (LFocks_rowMat (n := n) g).conjTranspose = LFocks_rowMat g.conjTranspose := by sorry
