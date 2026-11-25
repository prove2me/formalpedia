-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_G_smooth_K_finite_form_one_side
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.G.smooth_K_finite_form_one_side
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:05.421189+00:00
-- url     : https://prove2.me/theorems/a0fd8e5b-cda3-4916-943e-2f9d81e074c1
-- title:
--   G: smooth K finite form one side
-- statement:
--   The G construction uses the smooth K finite form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/AtForm.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/AtForm.lean#L15-L49

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscreteSeriesFormOneReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_K_finite_form_one_side

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

theorem Formalism.FourierDecayAlt.P.DDSmoothness.G.smooth_K_finite_form_one_side : CompanionTheory.D.Upq.BesselFunctionalConstruction.AtFormOneOfSteps := by sorry
