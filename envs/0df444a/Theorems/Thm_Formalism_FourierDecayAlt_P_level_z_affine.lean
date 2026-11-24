-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_level_z_affine
-- name    : Formalism.FourierDecayAlt.P.level_z_affine
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:49:14.375287+00:00
-- url     : https://prove2.me/theorems/228e432e-4fff-4087-b956-92fb0d05fec7
-- title:
--   P: level z affine
-- statement:
--   The P construction uses the level z affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L268-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L268-L268

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Ux4

theorem Formalism.FourierDecayAlt.P.level_z_affine : Formalism.FourierDecayAlt.U.ZjAffine := by sorry
