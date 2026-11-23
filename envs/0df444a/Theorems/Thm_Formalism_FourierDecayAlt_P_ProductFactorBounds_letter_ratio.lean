-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ProductFactorBounds_letter_ratio
-- name    : Formalism.FourierDecayAlt.P.ProductFactorBounds.letter_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:43.449295+00:00
-- url     : https://prove2.me/theorems/5765822f-38a2-4d3c-bee7-1484acaba778
-- title:
--   Product Factor Bounds: letter ratio
-- statement:
--   The Product Factor Bounds construction uses the letter ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L7-L33

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductFactorBounds
open Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.ProductFactorBounds.letter_ratio {K : Type} [Field K] (l : WLetter K) (Y : K) (h : OffPoles l Y) :
    (if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1)) /
      (if l.first then
        (if l.plus then (Y + 1 - l.pt) / (Y + 1 - l.pt - 1)
          else (l.pt - (Y + 1)) / (l.pt - (Y + 1) - 1)) else 1) = wFactor l Y := by sorry
