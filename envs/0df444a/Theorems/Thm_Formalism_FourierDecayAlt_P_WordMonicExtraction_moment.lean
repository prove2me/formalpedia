-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_moment
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.moment
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:50.590141+00:00
-- url     : https://prove2.me/theorems/c14766f8-6024-4c6a-851a-b1304f059ecd
-- title:
--   Word Monic Extraction: moment
-- statement:
--   The Word Monic Extraction construction uses the moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L30-L36

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

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.moment (d : ℕ) (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ) (hk : k ≤ d) :
    ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by sorry
