-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_prod
-- name    : Formalism.BranchingDeterminantCap.bmG_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:43.931845+00:00
-- url     : https://prove2.me/theorems/b81f0314-8313-4563-b13f-d0c4db2f92e2
-- title:
--   Branching Determinant Cap: bm G prod
-- statement:
--   The Branching Determinant Cap construction uses the bm G prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1991-L2000
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1991-L2000

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

theorem Formalism.BranchingDeterminantCap.bmG_prod {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} (s : Finset ι) (lam b : ι → Fin n → ℕ)
    (f : ι → MvPolynomial (Fin n × Fin n) R) (G : ι → BP R n)
    (h : ∀ i ∈ s, bmLift R n (lam i) (b i) (f i) (G i)) :
    bmLift R n (∑ i ∈ s, lam i) (∑ i ∈ s, b i) (∏ i ∈ s, f i) (∏ i ∈ s, G i) := by sorry
