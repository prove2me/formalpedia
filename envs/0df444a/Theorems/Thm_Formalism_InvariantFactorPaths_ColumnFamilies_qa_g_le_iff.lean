-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_g_le_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:03.549745+00:00
-- url     : https://prove2.me/theorems/a3148692-0652-440e-9c5f-fc9c541f7d44
-- title:
--   Column Families: qa g le iff
-- statement:
--   The Column Families construction uses the qa g le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L100-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L100-L124

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_le_iff {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n)
    (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ)) (a : Fin n) : qa_g m k p ≤ a ↔ k ≤ qa_S m a p := by sorry
