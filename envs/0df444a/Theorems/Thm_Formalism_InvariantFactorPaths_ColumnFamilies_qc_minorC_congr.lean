-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_minorC_congr
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_minorC_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:12.70062+00:00
-- url     : https://prove2.me/theorems/989cc34a-3b1e-4eb8-a3a6-cec833f77b10
-- title:
--   Column Families: qc minor C congr
-- statement:
--   The Column Families construction uses the qc minor C congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L89-L91

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_minorC_congr {n h h' : ℕ} (e : h = h') (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h)
    (hJ' : J.card = h') (hI' : I.card = h') : minorC J I hJ hI = minorC J I hJ' hI' := by sorry
