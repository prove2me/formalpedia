-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_ux_zjAffine
-- name    : Formalism.FourierDecayAlt.P.Ux4.ux_zjAffine
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:53:04.519062+00:00
-- url     : https://prove2.me/theorems/8e72690b-44b4-4b66-92f5-94a8c4b0e732
-- title:
--   Ux4: ux zj Affine
-- statement:
--   The Ux4 construction uses the ux zj Affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L231-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L231-L235

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4

theorem Formalism.FourierDecayAlt.P.Ux4.ux_zjAffine : ZjAffine := by sorry
