-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_bidet
-- name    : Formalism.BranchingDeterminantCap.bmG_bidet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:59.186534+00:00
-- url     : https://prove2.me/theorems/02041df4-bab2-4476-a9c6-d3638f3b50ef
-- title:
--   Branching Determinant Cap: bm G bidet
-- statement:
--   The Branching Determinant Cap construction uses the bm G bidet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2068-L2186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2068-L2186

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

theorem Formalism.BranchingDeterminantCap.bmG_bidet {R : Type*} [CommRing R] {n : ℕ} : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (lam : Fin n → ℕ), bmIL lam (shapeDeg sz) →
    ∃ G, bmLift R n lam (fun s => lam s - shapeDeg sz s) (bideterminant R sz hsz I) G := by sorry
