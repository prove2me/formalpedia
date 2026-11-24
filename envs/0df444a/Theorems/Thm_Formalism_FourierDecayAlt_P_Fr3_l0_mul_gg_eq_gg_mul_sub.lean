-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_l0_mul_gg_eq_gg_mul_sub
-- name    : Formalism.FourierDecayAlt.P.Fr3.l0_mul_gg_eq_gg_mul_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:00:57.007952+00:00
-- url     : https://prove2.me/theorems/a52c6db0-59e5-4c37-965c-942dccf8eb0f
-- title:
--   Fr3: l0 mul gg eq gg mul sub
-- statement:
--   The Fr3 construction uses the l0 mul gg eq gg mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L85-L90

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem Formalism.FourierDecayAlt.P.Fr3.l0_mul_gg_eq_gg_mul_sub (Y : ℂ) : L.l0 Y * L.GG = L.GG * (L.l0 Y - L.ζb * L.GGi) := by sorry
