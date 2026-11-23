-- Prove2me | Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_QS
-- name    : Formalism.LIFT.CocyclePolynomialSubmodules.mem_QS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:30.64113+00:00
-- url     : https://prove2.me/theorems/80fbf6fa-5fc8-4584-9252-945db3f76d50
-- title:
--   Cocycle Polynomial Submodules: mem QS
-- statement:
--   The Cocycle Polynomial Submodules construction uses the mem QS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L46-L46

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)

theorem Formalism.LIFT.CocyclePolynomialSubmodules.mem_QS {y : D} : y ∈ QS W ↔ W.QInv y := by sorry
