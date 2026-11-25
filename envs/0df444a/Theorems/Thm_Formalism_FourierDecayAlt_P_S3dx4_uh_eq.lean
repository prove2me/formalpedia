-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_uh_eq
-- name    : Formalism.FourierDecayAlt.P.S3dx4.uh_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:23.395146+00:00
-- url     : https://prove2.me/theorems/4fa2d6f7-78fa-518d-af9b-3f913c7fcad7
-- title:
--   S3dx4: uh eq
-- statement:
--   The S3dx4 construction uses the uh eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SigmaContOn.lean#L47-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SigmaContOn.lean#L47-L47

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

theorem Formalism.FourierDecayAlt.P.S3dx4.uh_eq (k r : ℕ) : PI.UpqRep.UH (PI.UpqRep.Hpk k r) = Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by sorry
