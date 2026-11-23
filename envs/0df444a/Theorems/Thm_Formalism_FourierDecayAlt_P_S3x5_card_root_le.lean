-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_root_le
-- name    : Formalism.FourierDecayAlt.P.S3x5.card_root_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:38.113865+00:00
-- url     : https://prove2.me/theorems/13d323fc-cd04-4614-ab6c-0c0a32d7aeb6
-- title:
--   S3x5: card root le
-- statement:
--   The S3x5 construction uses the card root le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L275-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L275-L284

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]

theorem Formalism.FourierDecayAlt.P.S3x5.card_root_le (p : K[X]) (hp : p ≠ 0) : Nat.card {x : K // p.eval x = 0} ≤ p.natDegree := by sorry
