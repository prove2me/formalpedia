-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_ndEv_rename
-- name    : Formalism.BranchingDeterminantCap.bmC_ndEv_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:43.598242+00:00
-- url     : https://prove2.me/theorems/5e28fe97-8976-452e-9443-96f6e707fbad
-- title:
--   Branching Determinant Cap: bm C nd Ev rename
-- statement:
--   The Branching Determinant Cap construction uses the bm C nd Ev rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L935-L940
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L935-L940

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bmC_ndEv_rename {R : Type*} [CommRing R] {r n : ℕ} (q : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (rename some q) = q := by sorry
