-- Prove2me | Theorems.Thm_Formalism_LIFT_uc_phi
-- name    : Formalism.LIFT.uc_phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:05.721342+00:00
-- url     : https://prove2.me/theorems/c68a7c49-afa2-4188-8a7d-1adedfbb1bf5
-- title:
--   LIFT: uc phi
-- statement:
--   The LIFT construction uses the uc phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L94-L100

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

theorem Formalism.LIFT.uc_phi (W : WD B M D) {n : D} (hn : n ∈ W.N) :
    W.QInv (B.Q • W.φ n - n) ∧ W.φ (B.X • n) - B.X • n = B.X • (B.Q • W.φ n - n) := by sorry
