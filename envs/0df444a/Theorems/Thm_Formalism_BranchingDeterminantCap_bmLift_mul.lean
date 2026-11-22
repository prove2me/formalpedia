-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_mul
-- name    : Formalism.BranchingDeterminantCap.bmLift_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:43:34.965028+00:00
-- url     : https://prove2.me/theorems/d90babee-74ff-40c2-ad25-1d037bfb6ed5
-- title:
--   Branching Determinant Cap: bm Lift mul
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1720-L1741
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1720-L1741

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

theorem Formalism.BranchingDeterminantCap.bmLift_mul {R : Type*} [CommRing R] {n : ℕ} {lam b lam' b' : Fin n → ℕ}
    {f f' : MvPolynomial (Fin n × Fin n) R} {G G' : BP R n} (h : bmLift R n lam b f G)
    (h' : bmLift R n lam' b' f' G') : bmLift R n (lam + lam') (b + b') (f * f') (G * G') := by sorry
