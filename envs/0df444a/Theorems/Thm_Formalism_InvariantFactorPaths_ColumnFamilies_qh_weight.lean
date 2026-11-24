-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_weight
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_weight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:49.958269+00:00
-- url     : https://prove2.me/theorems/2ea8fb0b-4dd6-4f2b-901a-141043330c67
-- title:
--   Column Families: qh weight
-- statement:
--   The Column Families construction uses the qh weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhMemDualWeyl.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhMemDualWeyl.lean#L87-L95

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_weight (d : Fin n × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) d = ⇑(Finsupp.mapDomain Prod.snd d) := by sorry
