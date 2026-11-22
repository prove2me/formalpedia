-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_minor
-- name    : Formalism.BranchingDeterminantCap.bmF_emb_minor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:18.022236+00:00
-- url     : https://prove2.me/theorems/fde1183d-2a04-448c-8d97-cfd8756564bc
-- title:
--   Branching Determinant Cap: bm F emb minor
-- statement:
--   The Branching Determinant Cap construction uses the bm F emb minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1770-L1776
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1770-L1776

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

theorem Formalism.BranchingDeterminantCap.bmF_emb_minor (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (c : Fin s → Fin n) :
    emb R n (Matrix.of fun p q : Fin s => (X (I p, c q) : MvPolynomial (Fin n × Fin n) R)).det =
      (Matrix.of fun p q : Fin s => (X ((I p).castSucc, c q) : BP R n)).det := by sorry
