-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_det_zpow_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_det_zpow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:59.590578+00:00
-- url     : https://prove2.me/theorems/0d8654fc-bf58-445c-aee5-9d0282edd935
-- title:
--   Column Families: qh det zpow mem
-- statement:
--   The Column Families construction uses the qh det zpow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L134-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L134-L148

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_det_zpow_mem (z : ℤ) : (((qhDet R n) ^ z : (GLCoord R n)ˣ) : GLCoord R n) ∈ inducedSections R (fun _ : Fin n => z) := by sorry
