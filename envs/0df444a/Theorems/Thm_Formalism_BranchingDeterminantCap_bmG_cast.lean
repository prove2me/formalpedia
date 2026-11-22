-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_cast
-- name    : Formalism.BranchingDeterminantCap.bmG_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:00.607922+00:00
-- url     : https://prove2.me/theorems/b0f88573-fef1-4cfc-a1d0-ceb482282a99
-- title:
--   Branching Determinant Cap: bm G cast
-- statement:
--   The Branching Determinant Cap construction uses the bm G cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1979-L1983
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1979-L1983

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

theorem Formalism.BranchingDeterminantCap.bmG_cast {R : Type*} [CommRing R] {n : ℕ} {lam b lam' b' : Fin n → ℕ}
    {f f' : MvPolynomial (Fin n × Fin n) R} {G G' : BP R n} (h : bmLift R n lam b f G)
    (h1 : lam = lam') (h2 : b = b') (h3 : f = f') (h4 : G = G') : bmLift R n lam' b' f' G' := by sorry
