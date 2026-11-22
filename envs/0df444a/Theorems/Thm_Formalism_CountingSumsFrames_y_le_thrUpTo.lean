-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_y_le_thrUpTo
-- name    : Formalism.CountingSumsFrames.y_le_thrUpTo
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:32.362446+00:00
-- url     : https://prove2.me/theorems/17bbc0ed-b089-44e4-afd5-60b7c050c0e6
-- title:
--   Counting Sums Frames: y le thr Up To
-- statement:
--   The Counting Sums Frames construction uses the y le thr Up To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L286-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L286-L295

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.y_le_thrUpTo {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) :
    Y p (r := r) LL T.J T.thr ≤ Y p (r := r) LL T.J (T.thrUpTo i) := by sorry
