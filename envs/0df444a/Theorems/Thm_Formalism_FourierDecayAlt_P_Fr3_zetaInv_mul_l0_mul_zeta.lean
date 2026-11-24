-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zetaInv_mul_l0_mul_zeta
-- name    : Formalism.FourierDecayAlt.P.Fr3.zetaInv_mul_l0_mul_zeta
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:04:22.046585+00:00
-- url     : https://prove2.me/theorems/1a67919d-ffe2-4ea6-b8a2-293de06a27b3
-- title:
--   Fr3: zeta Inv mul l0 mul zeta
-- statement:
--   The Fr3 construction uses the zeta Inv mul l0 mul zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L75-L83

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

theorem Formalism.FourierDecayAlt.P.Fr3.zetaInv_mul_l0_mul_zeta (Y : ℂ) : L.ζi * L.l0 Y * L.ζ = L.l0 Y - L.ζi := by sorry
