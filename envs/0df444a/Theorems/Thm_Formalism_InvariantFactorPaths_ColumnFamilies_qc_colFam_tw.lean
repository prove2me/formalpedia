-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colFam_tw
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_colFam_tw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:05.671934+00:00
-- url     : https://prove2.me/theorems/fcbece96-873e-44bb-ae7b-68fa57249d46
-- title:
--   Column Families: qc col Fam tw
-- statement:
--   The Column Families construction uses the qc col Fam tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L133-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L133-L159

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
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
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_colFam_tw (M M' : GLMod n) (ε : ℤ) (e : M'.ι ≃ M.ι)
    (hA : ∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j))
    (CF : ColFam M) : Nonempty (ColFam M') := by sorry
