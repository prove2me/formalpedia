-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_cl
-- name    : Formalism.FourierDecayAlt.P.G2.blk_cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:45.329159+00:00
-- url     : https://prove2.me/theorems/9c42d92d-4498-412e-81d4-2ce52fe902b1
-- title:
--   G2: blk cl
-- statement:
--   The G2 construction uses the blk cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L23-L25

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

theorem Formalism.FourierDecayAlt.P.G2.blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by sorry
