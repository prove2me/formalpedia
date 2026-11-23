-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_pm_le
-- name    : Formalism.FourierDecayAlt.P.S3x5.card_pm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:32.968783+00:00
-- url     : https://prove2.me/theorems/9684e25c-8f38-4fdd-99aa-53a5f1005244
-- title:
--   S3x5: card pm le
-- statement:
--   The S3x5 construction uses the card pm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L286-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L286-L299

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

theorem Formalism.FourierDecayAlt.P.S3x5.card_pm_le {q : ℕ} (hq : 2 ≤ q) (e : K) : Nat.card {x : K // x ^ q + e * x = 0} ≤ q := by sorry
