-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mul_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:51.204393+00:00
-- url     : https://prove2.me/theorems/4502ad50-579e-4993-843c-b2988d00eb23
-- title:
--   Column Families: qh mul mem
-- statement:
--   The Column Families construction uses the qh mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L108-L114

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_mul_mem {mu mu' : Fin n → ℤ} {f f' : GLCoord R n} (hf : f ∈ inducedSections R mu) (hf' : f' ∈ inducedSections R mu') :
    f * f' ∈ inducedSections R (mu + mu') := by sorry
