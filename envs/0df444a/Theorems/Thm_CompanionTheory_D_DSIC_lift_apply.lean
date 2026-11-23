-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- name    : CompanionTheory.D.DSIC.lift_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:51.434007+00:00
-- url     : https://prove2.me/theorems/f3904998-9326-45dd-ad42-264277116963
-- title:
--   DSIC: lift apply
-- statement:
--   The DSIC construction uses the lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CapelliDeterminantBlockProduct.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CapelliDeterminantBlockProduct.lean#L45-L46

import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)
open PI.DSInfCharCap (dsigC actU Egl)
open PI.PhMeasCore (dsig smoothVecs)
variable {n : ℕ}
variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem CompanionTheory.D.DSIC.lift_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Ch ε V)
    (A : Finset (NC ε)) : lift ε T x A = T (x A) := by sorry

attribute [defeq] CompanionTheory.D.DSIC.lift_apply
