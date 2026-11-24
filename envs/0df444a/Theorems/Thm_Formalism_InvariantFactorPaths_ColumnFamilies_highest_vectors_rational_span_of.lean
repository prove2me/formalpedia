-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_highest_vectors_rational_span_of
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.highest_vectors_rational_span_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:07.666948+00:00
-- url     : https://prove2.me/theorems/bc67e0c6-811b-4666-b147-30f3c423409e
-- title:
--   Column Families: highest vectors rational span of
-- statement:
--   The Column Families construction uses the highest vectors rational span of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L71-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L71-L160

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.highest_vectors_rational_span_of : LemmaA → HighestVectorsRationalSpan := by sorry
