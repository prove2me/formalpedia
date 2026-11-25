-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_G_zeroCase_of
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.zeroCase_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:51:56.046672+00:00
-- url     : https://prove2.me/theorems/c39f5725-4bdc-592a-91ec-5568f8018c26
-- title:
--   G: zero Case of
-- statement:
--   The G construction uses the zero Case of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/VanishingOfL2Equivariant.lean#L49-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/VanishingOfL2Equivariant.lean#L49-L106

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_VanishingOfL2Equivariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_zeroCase_of

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
set_option maxHeartbeats 3200000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.zeroCase_of (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hSch : SchurH) : CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCase := by sorry
