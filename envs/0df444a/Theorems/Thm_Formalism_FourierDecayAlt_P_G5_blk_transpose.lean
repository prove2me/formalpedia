-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_transpose
-- name    : Formalism.FourierDecayAlt.P.G5.blk_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:48.687783+00:00
-- url     : https://prove2.me/theorems/b9a320a9-7db8-4b3b-a7a4-185c93bdd8a7
-- title:
--   G5: blk transpose
-- statement:
--   The G5 construction uses the blk transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L171-L175

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

theorem Formalism.FourierDecayAlt.P.G5.blk_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    (blk A b a e)ᵀ = blk Aᵀ a b e := by sorry
