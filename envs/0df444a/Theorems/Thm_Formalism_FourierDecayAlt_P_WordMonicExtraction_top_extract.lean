-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_top_extract
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.top_extract
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:49.735809+00:00
-- url     : https://prove2.me/theorems/a998a3ba-dd54-424f-9456-73f15c591941
-- title:
--   Word Monic Extraction: top extract
-- statement:
--   The Word Monic Extraction construction uses the top extract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L62-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L62-L73

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

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.top_extract {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (h : IsTopCoeff W d c) (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) : ∑ i, ((lagCo y i : ℝ) : ℂ) * W (y i) = c := by sorry
