-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_wMat_ne_zero
-- name    : Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:57.351807+00:00
-- url     : https://prove2.me/theorems/550168fe-d620-486e-8adb-973c98e992ad
-- title:
--   G2: det w Mat ne zero
-- statement:
--   The G2 construction uses the det w Mat ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L92-L97

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
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
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G2
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (n : ℕ) : (wMat n).det ≠ 0 := by sorry
