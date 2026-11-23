-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_vecMul
-- name    : Formalism.FourierDecayAlt.P.G5.mp_vecMul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:17.311987+00:00
-- url     : https://prove2.me/theorems/4368f38a-0eb0-4c0a-a8d6-9bc5382166d0
-- title:
--   G5: mp vec Mul
-- statement:
--   The G5 construction uses the mp vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L40-L43

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

theorem Formalism.FourierDecayAlt.P.G5.mp_vecMul (β : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    MeasurePreserving (fun x : ι → ℂ => x ᵥ* M) (muPi β ι) (muPi β ι) := by sorry
