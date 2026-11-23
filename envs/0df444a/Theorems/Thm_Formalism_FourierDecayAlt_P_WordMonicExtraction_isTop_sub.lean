-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_isTop_sub
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.isTop_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:43.902811+00:00
-- url     : https://prove2.me/theorems/22826290-1855-4e0c-8f47-c71c4d8b7ad1
-- title:
--   Word Monic Extraction: is Top sub
-- statement:
--   The Word Monic Extraction construction uses the is Top sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L89-L95

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

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.isTop_sub {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by sorry
