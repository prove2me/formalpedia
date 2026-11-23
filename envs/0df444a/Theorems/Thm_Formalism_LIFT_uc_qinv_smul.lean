-- Prove2me | Theorems.Thm_Formalism_LIFT_uc_qinv_smul
-- name    : Formalism.LIFT.uc_qinv_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:44.849321+00:00
-- url     : https://prove2.me/theorems/8fe3d7ac-c411-456e-bd1e-7a2b81e040cc
-- title:
--   LIFT: uc qinv smul
-- statement:
--   The LIFT construction uses the uc qinv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L36-L39

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

theorem Formalism.LIFT.uc_qinv_smul (W : WD B M D) (r : ℤ_[ℓ]) {x : D} (hx : W.QInv x) : W.QInv (r • x) := by sorry
