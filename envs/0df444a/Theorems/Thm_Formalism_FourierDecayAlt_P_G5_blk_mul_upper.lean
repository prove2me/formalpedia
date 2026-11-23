-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_mul_upper
-- name    : Formalism.FourierDecayAlt.P.G5.blk_mul_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:54.533222+00:00
-- url     : https://prove2.me/theorems/5e4400ad-b43c-4549-a25c-f1942567b86a
-- title:
--   G5: blk mul upper
-- statement:
--   The G5 construction uses the blk mul upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L162-L164

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

theorem Formalism.FourierDecayAlt.P.G5.blk_mul_upper {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b b' : Fin n → ℂ) :
    blk A b 0 1 * blk A' b' 0 1 = blk (A * A') (A *ᵥ b' + b) 0 1 := by sorry
