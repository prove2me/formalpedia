-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_lt_colH_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_lt_colH_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:30.905568+00:00
-- url     : https://prove2.me/theorems/0ba9c4b9-ce88-46f3-aebd-f88ccf84250b
-- title:
--   Column Families: qh lt col H iff
-- statement:
--   The Column Families construction uses the qh lt col H iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L11-L36

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
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
variable {n : ℕ} {R : Type} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by sorry
