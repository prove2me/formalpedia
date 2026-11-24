-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_init_congr
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_init_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:48.29773+00:00
-- url     : https://prove2.me/theorems/86632bc5-0467-436e-a18f-342d9eb4295e
-- title:
--   Column Families: qc init congr
-- statement:
--   The Column Families construction uses the qc init congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L50-L52

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_init_congr {n h h' : ℕ} (e : h = h') (hn : h ≤ n) (hn' : h' ≤ n) :
    (univ : Finset (Fin h)).map (Fin.castLEEmb hn) = (univ : Finset (Fin h')).map (Fin.castLEEmb hn') := by sorry
