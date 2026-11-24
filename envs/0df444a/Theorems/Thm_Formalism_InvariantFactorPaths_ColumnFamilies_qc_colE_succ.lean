-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colE_succ
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_colE_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:12.415941+00:00
-- url     : https://prove2.me/theorems/a22dd703-d62d-4f60-a6c9-c8be16bab853
-- title:
--   Column Families: qc col E succ
-- statement:
--   The Column Families construction uses the qc col E succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L59-L62

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_colE_succ (mu : Fin n → ℤ) (ε : ℤ) (c : ↥(TCols mu)) (hc : c.1 + 1 ∈ TCols mu)
    (hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε)) :
    qc_colE mu ε ⟨c.1 + 1, hc⟩ = ⟨(qc_colE mu ε c).1 + 1, hc'⟩ := by sorry
