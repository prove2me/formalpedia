-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_S_le
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_S_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:18.078485+00:00
-- url     : https://prove2.me/theorems/42ab0851-d612-4fcd-88c9-9c4a5551e0c3
-- title:
--   Column Families: qa S le
-- statement:
--   The Column Families construction uses the qa S le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L19-L21

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_S_le {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : qa_S m a p ≤ ∑ b : Fin n, m (b, p) := by sorry
