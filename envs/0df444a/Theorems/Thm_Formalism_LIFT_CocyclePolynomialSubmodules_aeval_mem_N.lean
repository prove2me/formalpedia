-- Prove2me | Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_mem_N
-- name    : Formalism.LIFT.CocyclePolynomialSubmodules.aeval_mem_N
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:20.671109+00:00
-- url     : https://prove2.me/theorems/a6f19952-2674-42a4-b5e2-56eccdf0956e
-- title:
--   Cocycle Polynomial Submodules: aeval mem N
-- statement:
--   The Cocycle Polynomial Submodules construction uses the aeval mem N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L94-L95

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

theorem Formalism.LIFT.CocyclePolynomialSubmodules.aeval_mem_N (p : Polynomial ℤ_[ℓ]) {y : D} (hy : y ∈ W.N) :
    Polynomial.aeval W.γ p y ∈ W.N := by sorry
