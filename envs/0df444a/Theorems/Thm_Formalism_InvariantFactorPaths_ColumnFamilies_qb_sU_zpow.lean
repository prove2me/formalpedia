-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_sU_zpow
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_sU_zpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:56.149125+00:00
-- url     : https://prove2.me/theorems/c1f7811e-56f5-4a1d-a8cf-42517e3f6e7d
-- title:
--   Column Families: qb s U zpow
-- statement:
--   The Column Families construction uses the qb s U zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L80-L82

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_sU_zpow (w : Fin n → ℤ) (z : ℤ) : qb_sU w ^ z = qb_sU (z • w) := by sorry
