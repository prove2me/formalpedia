-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_lowRow_mul
-- name    : Formalism.FourierDecayAlt.P.G5.lowRow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:16.765569+00:00
-- url     : https://prove2.me/theorems/d52c66ee-20ad-48c8-8632-9ddd81fb001f
-- title:
--   G5: low Row mul
-- statement:
--   The G5 construction uses the low Row mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L166-L169

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.lowRow_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) :
    lowRow a * blk A 0 0 1 = blk A 0 (a ᵥ* A) 1 := by sorry
