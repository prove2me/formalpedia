-- Prove2me | Theorems.Thm_Formalism_LIFT_d1_sub_sub
-- name    : Formalism.LIFT.d1_sub_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:05.129562+00:00
-- url     : https://prove2.me/theorems/9ab5a98e-4a12-4dde-8265-e0104bc8030b
-- title:
--   LIFT: d1 sub sub
-- statement:
--   The LIFT construction uses the d1 sub sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L46-L50

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
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
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]

theorem Formalism.LIFT.d1_sub_sub (W : WD B M D) (y z y' z' : D) :
    W.d1 (y - y') (z - z') = W.d1 y z - W.d1 y' z' := by sorry
