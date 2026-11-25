-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_ccleQ_mono_c
-- name    : Formalism.FourierDecayAlt.P.CutBP.ccleQ_mono_c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:21:31.395824+00:00
-- url     : https://prove2.me/theorems/7cd5175c-1c29-437d-9555-6d1003bad385
-- title:
--   Cut BP: ccle Q mono c
-- statement:
--   The Cut BP construction uses the ccle Q mono c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutNFApxDomThQ.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutNFApxDomThQ.lean#L20-L21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutNFApxDomThQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutBP.ccleQ_mono_c {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b b' : ℝ} (h : B.CCle A m F b) (hb : b ≤ b') : B.CCle A m F b' := by sorry
