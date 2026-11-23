-- Prove2me | Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_pres
-- name    : Formalism.LIFT.CocyclePolynomialSubmodules.aeval_pres
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:51.748944+00:00
-- url     : https://prove2.me/theorems/00671db5-61dd-4ee6-9ee9-a0e40e7b0fd2
-- title:
--   Cocycle Polynomial Submodules: aeval pres
-- statement:
--   The Cocycle Polynomial Submodules construction uses the aeval pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L10-L27

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

theorem Formalism.LIFT.CocyclePolynomialSubmodules.aeval_pres {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (f : E →ₗ[R] E)
    (S : Submodule R E) (hf : ∀ y ∈ S, f y ∈ S) (p : Polynomial R) :
    ∀ y ∈ S, Polynomial.aeval f p y ∈ S := by sorry
