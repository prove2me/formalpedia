-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qhDet_val
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qhDet_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:33.972007+00:00
-- url     : https://prove2.me/theorems/1ae69555-d9de-4653-8b55-258da7abf5d4
-- title:
--   Column Families: qh Det val
-- statement:
--   The Column Families construction uses the qh Det val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L128-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L128-L128

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qhDet_val : ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) = algebraMap _ _ (genMat R n).det := by sorry
