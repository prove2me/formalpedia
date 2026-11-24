-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_hpk_eq
-- name    : Formalism.FourierDecayAlt.P.S3dx4.hpk_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:02.218625+00:00
-- url     : https://prove2.me/theorems/4e78b445-f34d-492a-8801-f1626f87ee78
-- title:
--   S3dx4: hpk eq
-- statement:
--   The S3dx4 construction uses the hpk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SigmaContOn.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SigmaContOn.lean#L45-L45

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
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
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem Formalism.FourierDecayAlt.P.S3dx4.hpk_eq (k r : ℕ) : PI.UpqRep.Hpk k r = Formalism.QuantumDeterminants.Hpk k r := by sorry
