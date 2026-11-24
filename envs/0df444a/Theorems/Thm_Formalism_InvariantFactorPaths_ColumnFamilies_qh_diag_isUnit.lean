-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_diag_isUnit
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_diag_isUnit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:15.912274+00:00
-- url     : https://prove2.me/theorems/a194dfc8-6785-44d6-bcbd-fb22d3807946
-- title:
--   Column Families: qh diag is Unit
-- statement:
--   The Column Families construction uses the qh diag is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L36-L40

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_diag_isUnit {R' : Type} [CommRing R'] (b : GL (Fin n) R')
    (hb : ∀ a c : Fin n, a < c → b.val a c = 0) (a : Fin n) : IsUnit (b.val a a) := by sorry
