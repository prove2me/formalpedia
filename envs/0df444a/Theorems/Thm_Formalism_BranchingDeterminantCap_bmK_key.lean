-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_key
-- name    : Formalism.BranchingDeterminantCap.bmK_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:59.830939+00:00
-- url     : https://prove2.me/theorems/4d370b62-c379-413f-9139-c1647117a4c8
-- title:
--   Branching Determinant Cap: bm K key
-- statement:
--   The Branching Determinant Cap construction uses the bm K key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2497-L2510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2497-L2510

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

theorem Formalism.BranchingDeterminantCap.bmK_key {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (f : MvPolynomial (Fin n × Fin n) R) (G G' : BP R n)
    (h : bmLift R n lam (fun s => lam s - sg s) f G) (h' : bmLift R n lam (fun s => lam s - sg s) f G') :
    bmZop R n lam sg G = bmZop R n lam sg G' := by sorry
