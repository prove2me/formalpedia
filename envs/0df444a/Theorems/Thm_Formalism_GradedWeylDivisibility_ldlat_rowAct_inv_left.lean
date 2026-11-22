-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_rowAct_inv_left
-- name    : Formalism.GradedWeylDivisibility.ldlat_rowAct_inv_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:21.129738+00:00
-- url     : https://prove2.me/theorems/61b697cf-5935-4934-b7c6-237c472a334b
-- title:
--   Graded Weyl Divisibility: ldlat row Act inv left
-- statement:
--   The Graded Weyl Divisibility construction uses the ldlat row Act inv left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDlatLemmas.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDlatLemmas.lean#L17-L20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
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

theorem Formalism.GradedWeylDivisibility.ldlat_rowAct_inv_left (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g (rowAct K g⁻¹ x) = x := by sorry
