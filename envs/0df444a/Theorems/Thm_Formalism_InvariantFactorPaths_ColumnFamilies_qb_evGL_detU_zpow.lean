-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_detU_zpow
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_detU_zpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:30.977412+00:00
-- url     : https://prove2.me/theorems/d2a5a3a2-a2f1-47b3-8788-8b1ad299cbc5
-- title:
--   Column Families: qb ev GL det U zpow
-- statement:
--   The Column Families construction uses the qb ev GL det U zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L30-L35

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_detU_zpow {R : Type} [CommRing R] (g : GL (Fin n) R) (u : Rˣ) (hu : (u : R) = g.val.det) (z : ℤ) :
    evGL g ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((u ^ z : Rˣ) : R) := by sorry
