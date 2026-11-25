-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_GC_discrete_form_one_side
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.GC.discrete_form_one_side
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:16.739332+00:00
-- url     : https://prove2.me/theorems/7a046616-c6d3-5d71-86f9-f47095d6c489
-- title:
--   GC: discrete form one side
-- statement:
--   The GC construction uses the discrete form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/DDFormC.lean#L15-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/DDFormC.lean#L15-L45

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormAdmOneOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_DDFormC
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
open Formalism.FourierDecayAlt.P.DDSmoothness.GC

theorem Formalism.FourierDecayAlt.P.DDSmoothness.GC.discrete_form_one_side : CompanionTheory.D.Upq.BesselFunctionalConstruction.C.DDFormOneOfSteps := by sorry
