-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Slt
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_Slt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:13.86382+00:00
-- url     : https://prove2.me/theorems/911aeb73-2d92-43f8-8740-df70ddb75ecf
-- title:
--   Column Families: qa Slt
-- statement:
--   The Column Families construction uses the qa Slt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L34-L51

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_Slt {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) :
    (∑ b : Fin n with b < a, m (b, p)) = 0 ∨ ∃ b, b < a ∧ (∑ b : Fin n with b < a, m (b, p)) = qa_S m b p := by sorry
