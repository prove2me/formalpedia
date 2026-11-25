-- Prove2me | Theorems.Thm_CompanionTheory_Lime_BM_uniqGap_of_uniq
-- name    : CompanionTheory.Lime.BM.uniqGap_of_uniq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:23.804121+00:00
-- url     : https://prove2.me/theorems/99956d17-acbd-46f6-b802-86c6dd5d47da
-- title:
--   BM: uniq Gap of uniq
-- statement:
--   The BM construction uses the uniq Gap of uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean#L28-L29

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps
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

theorem CompanionTheory.Lime.BM.uniqGap_of_uniq (h : PI.BesselMapUniq.BesselMapUniq) : UniqGap := by sorry
