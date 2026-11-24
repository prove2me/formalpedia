-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_mulVec_bvec
-- name    : Formalism.FourierDecayAlt.P.FlagSpanVanishing.mulVec_bvec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:30.850275+00:00
-- url     : https://prove2.me/theorems/f6801dce-37c8-4865-b385-2d65763902a9
-- title:
--   Flag Span Vanishing: mul Vec bvec
-- statement:
--   The Flag Span Vanishing construction uses the mul Vec bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L27-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FlagSpanVanishing.mulVec_bvec (M : B.Mat k r) (x : Fin (2 * r + k + 1)) : M *ᵥ bvec x = fun i => M i x := by sorry
