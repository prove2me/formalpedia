-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_isWH_of_comm
-- name    : Formalism.BranchingDeterminantCap.bm_isWH_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:39.769259+00:00
-- url     : https://prove2.me/theorems/b3954a81-e813-4d88-8424-a09ada394c76
-- title:
--   Branching Determinant Cap: bm is WH of comm
-- statement:
--   The Branching Determinant Cap construction uses the bm is WH of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L147-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L147-L155

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

theorem Formalism.BranchingDeterminantCap.bm_isWH_of_comm {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (β : B)
    (x : Module.End R (MvPolynomial σ R))
    (hx : Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) x)
    (F : MvPolynomial σ R) (hF : IsWeightedHomogeneous w F β) : IsWeightedHomogeneous w (x F) β := by sorry
