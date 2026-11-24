-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_ev_zero_of_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_ev_zero_of_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:58:45.960872+00:00
-- url     : https://prove2.me/theorems/0326066f-4245-4f15-9972-9ced2b56e151
-- title:
--   Column Families: qb ev zero of mem
-- statement:
--   The Column Families construction uses the qb ev zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L11-L14

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
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
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_ev_zero_of_mem {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] {pi : Set (Fin n → ℤ)}
    (hpi : DomLowerSet pi) {j : CF.J} (hj : CF.mu j ∈ pi) (I : TIdx (CF.mu j)) {mu : Fin n → ℤ}
    (hmu : Dominant mu) (hout : mu ∉ pi) : qb_ev M F mu (fun i => (CF.vec j I i : F)) = 0 := by sorry
