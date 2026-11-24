-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_f_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_f_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:58.753145+00:00
-- url     : https://prove2.me/theorems/6c36f33a-0533-4f4b-8834-4656e19c5004
-- title:
--   Column Families: qd f mem
-- statement:
--   The Column Families construction uses the qd f mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L46-L48

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_f_mem {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) :
    qd_f CF a j ∈ Submodule.span ℚ (Set.range fun I : TIdx (CF.mu j) => mapCoord ℚ (brk (CF.mu j) I)) := by sorry
