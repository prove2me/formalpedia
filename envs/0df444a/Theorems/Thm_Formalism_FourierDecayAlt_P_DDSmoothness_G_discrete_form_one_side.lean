-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_G_discrete_form_one_side
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.G.discrete_form_one_side
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:46:30.745174+00:00
-- url     : https://prove2.me/theorems/145db3ba-7d98-5ec1-a7df-c4d82bede4a2
-- title:
--   G: discrete form one side
-- statement:
--   The G construction uses the discrete form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/DDForm.lean#L15-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/DDForm.lean#L15-L46

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_DDForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_discrete_form_one_side

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.DDSmoothness.G

theorem Formalism.FourierDecayAlt.P.DDSmoothness.G.discrete_form_one_side : CompanionTheory.D.Upq.BesselFunctionalConstruction.DDFormOneOfSteps := by sorry
