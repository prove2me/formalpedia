-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_word_weight_formula
-- name    : Formalism.FourierDecayAlt.P.word_weight_formula
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:26.811306+00:00
-- url     : https://prove2.me/theorems/b6087b27-c543-4fee-81f8-7c75e3d25715
-- title:
--   P: word weight formula
-- statement:
--   The P construction uses the word weight formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L153-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L153-L162

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.ProductFactorBounds

theorem Formalism.FourierDecayAlt.P.word_weight_formula : Formalism.FourierDecayAlt.F7.WordWeight := by sorry
