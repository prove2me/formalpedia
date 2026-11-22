-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_equiv_apply
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_equiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:37.865003+00:00
-- url     : https://prove2.me/theorems/cc70014e-3896-4ed1-92ba-8f16ee8f9b3e
-- title:
--   Column Families: qb equiv apply
-- statement:
--   The Column Families construction uses the qb equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L119-L121

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_equiv_apply {M : GLMod n} (CF : ColFam M) (j : CF.J) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, M.A i k * (CF.ph j k K : GLCoord ℤ n) = ∑ K', (CF.ph j i K' : GLCoord ℤ n) * TMat (CF.mu j) K' K := by sorry
