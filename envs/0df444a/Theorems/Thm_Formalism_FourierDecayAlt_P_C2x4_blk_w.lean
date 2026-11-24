-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_blk_w
-- name    : Formalism.FourierDecayAlt.P.C2x4.blk_w
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:21.1257+00:00
-- url     : https://prove2.me/theorems/209a5baf-106f-4337-9bcf-52cd3320d33b
-- title:
--   C2x4: blk w
-- statement:
--   The C2x4 construction uses the blk w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L91-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L91-L106

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
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
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x4.blk_w (w : Equiv.Perm (Fin m)) (a : Fin m) : blk w (w a) = blk w a := by sorry
