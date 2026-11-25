-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_G_bessel_nonvanishing_from_L2
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.G.bessel_nonvanishing_from_L2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:24.114294+00:00
-- url     : https://prove2.me/theorems/a9f7edb2-b2c8-4e1f-a70a-37f8c14ff5ed
-- title:
--   G: bessel nonvanishing from L2
-- statement:
--   The G construction uses the bessel nonvanishing from L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/BesselNonvanishingFromL2.lean#L15-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/BesselNonvanishingFromL2.lean#L15-L152

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNonvanishingFromL2
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingFromL2
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_bessel_nonvanishing_from_L2

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.G

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.G.bessel_nonvanishing_from_L2 : CompanionTheory.D.Upq.BesselFunctionalConstruction.BesselNonvanishingReduction := by sorry
