-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_S_mono
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_S_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:44.180292+00:00
-- url     : https://prove2.me/theorems/51629c51-d69d-49fc-b5eb-e0f9adf8f063
-- title:
--   Column Families: qa S mono
-- statement:
--   The Column Families construction uses the qa S mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L11-L17

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_S_mono {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (p : Fin n) {a a' : Fin n} (h : a ≤ a') :
    qa_S m a p ≤ qa_S m a' p := by sorry
