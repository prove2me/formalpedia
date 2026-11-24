-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_nu_cast
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_nu_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:29.977799+00:00
-- url     : https://prove2.me/theorems/f1e3fb39-3206-43be-a868-e317e63f3231
-- title:
--   Column Families: qa nu cast
-- statement:
--   The Column Families construction uses the qa nu cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L132-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L132-L136

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_nu_cast {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (p : Fin n) :
    (qa_nu mu p : ℤ) = mu p - mu (lastIdx n) := by sorry
