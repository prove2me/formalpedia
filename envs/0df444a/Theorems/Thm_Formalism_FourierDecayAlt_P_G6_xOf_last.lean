-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G6_xOf_last
-- name    : Formalism.FourierDecayAlt.P.G6.xOf_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:39.073473+00:00
-- url     : https://prove2.me/theorems/de1b3b06-6a9d-462e-bbd4-3e576b00a31f
-- title:
--   G6: x Of last
-- statement:
--   The G6 construction uses the x Of last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L27-L29

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G6.xOf_last {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) :
    xOf X B (Fin.last m) = B (Fin.last m) := by sorry
