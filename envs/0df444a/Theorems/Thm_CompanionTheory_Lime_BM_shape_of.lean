-- Prove2me | Theorems.Thm_CompanionTheory_Lime_BM_shape_of
-- name    : CompanionTheory.Lime.BM.shape_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:46:42.127586+00:00
-- url     : https://prove2.me/theorems/482b728f-aa46-5249-8426-640f29ca4a1f
-- title:
--   BM: shape of
-- statement:
--   The BM construction uses the shape of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean#L107-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean#L107-L182

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_shape_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open CompanionTheory CompanionTheory.Lime CompanionTheory.Lime.BM
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.DDSmoothness

theorem CompanionTheory.Lime.BM.shape_of (hU : UniqGap) (hPsi : PsiConst) (hSch : SchurH) (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hBB : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeBessel) : Shape := by sorry
