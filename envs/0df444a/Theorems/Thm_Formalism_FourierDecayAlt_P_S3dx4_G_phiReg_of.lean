-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_G_phiReg_of
-- name    : Formalism.FourierDecayAlt.P.S3dx4.G.phiReg_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:43.843967+00:00
-- url     : https://prove2.me/theorems/907d5008-e620-5d1a-9b05-b538c333d4f3
-- title:
--   G: phi Reg of
-- statement:
--   The G construction uses the phi Reg of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/PhiReg.lean#L14-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/PhiReg.lean#L14-L85

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_PhiReg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_phiReg_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.S3dx4.G

theorem Formalism.FourierDecayAlt.P.S3dx4.G.phiReg_of (hSch : SchurH) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hGG : GrowthG) (hDD : CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD) (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) :
    CompanionTheory.D.Upq.BesselFunctionalConstruction.PhiReg := by sorry
