-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_BesselFunctionalConstruction_kFinForm_of
-- name    : CompanionTheory.D.Upq.BesselFunctionalConstruction.kFinForm_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:46.581211+00:00
-- url     : https://prove2.me/theorems/9ab53b44-bc77-5075-99d3-ee517045a3f8
-- title:
--   Bessel Functional Construction: k Fin Form of
-- statement:
--   The Bessel Functional Construction construction uses the k Fin Form of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/KFinFormOf.lean#L71-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/KFinFormOf.lean#L71-L91

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_KFinFormOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_kFinForm_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.BesselFunctionalConstruction
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness

theorem CompanionTheory.D.Upq.BesselFunctionalConstruction.kFinForm_of (hBC : BeConv) (hBB : BeBessel) : KFinForm := by sorry
