-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_kill
-- name    : Formalism.BranchingDeterminantCap.bmK_kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:30.517806+00:00
-- url     : https://prove2.me/theorems/bef944c5-12d1-4e6c-85b0-5262027a7b07
-- title:
--   Branching Determinant Cap: bm K kill
-- statement:
--   The Branching Determinant Cap construction uses the bm K kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2483-L2491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2483-L2491

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

theorem Formalism.BranchingDeterminantCap.bmK_kill {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (G : BP R n)
    (hG : G ∈ bmW R n lam (∑ s, (lam s - sg s)))
    (h0 : zcomp R n (fun s => ((lam s - sg s : ℕ) : ℤ)) G = 0) : bmZop R n lam sg G = 0 := by sorry
