-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_g_step
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:02.064871+00:00
-- url     : https://prove2.me/theorems/f5864a8c-8470-463d-9af4-3b49f3769eb5
-- title:
--   Column Families: qa g step
-- statement:
--   The Column Families construction uses the qa g step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L144-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L144-L155

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_step {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (k : ℤ) (hk1 : 1 ≤ k)
    (p p' : Fin n) (hpp : p'.val = p.val + 1) (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ))
    (hk' : k ≤ (∑ b : Fin n, m (b, p') : ℕ)) : qa_g m k p < qa_g m k p' := by sorry
