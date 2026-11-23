-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_VacLev_sharp
-- name    : Formalism.BranchingDeterminantCap.VacLev.sharp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:21.712897+00:00
-- url     : https://prove2.me/theorems/f01d223c-5f9c-4f6f-93ba-66e6cdce42ef
-- title:
--   Vac Lev: sharp
-- statement:
--   The Vac Lev construction uses the sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/GlobalBoundRefinements.lean#L515-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/GlobalBoundRefinements.lean#L515-L533

import Definitions.Def_Formalism_BranchSandwichDivisors_DualLevelType
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.VacLev

theorem Formalism.BranchingDeterminantCap.VacLev.sharp :
    (1 : ℚ) ∈ A.map (io.restrictScalars ℤ) ⊓
      (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).restrictScalars ℤ ∧
    (1 : ℚ) ∉ (A ⊓ (LinearMap.range e0).restrictScalars ℤ).map (io.restrictScalars ℤ) ∧
    ((2 : ℕ) : ℤ) • (1 : ℚ) ∈
      (A ⊓ (LinearMap.range e0).restrictScalars ℤ).map (io.restrictScalars ℤ) := by sorry
