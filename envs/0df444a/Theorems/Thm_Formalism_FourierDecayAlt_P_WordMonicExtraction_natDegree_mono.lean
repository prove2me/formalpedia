-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_natDegree_mono
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.natDegree_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:28.123347+00:00
-- url     : https://prove2.me/theorems/fdb00b2d-f73b-49b2-91ce-b6fdfe1b612a
-- title:
--   Word Monic Extraction: nat Degree mono
-- statement:
--   The Word Monic Extraction construction uses the nat Degree mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L104-L108

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.natDegree_mono (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by sorry
