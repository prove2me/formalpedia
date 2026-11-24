-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_det_eval
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_eval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:34.632473+00:00
-- url     : https://prove2.me/theorems/0e5d0be2-9f25-4286-89cc-1d6243389475
-- title:
--   Column Families: qk det eval
-- statement:
--   The Column Families construction uses the qk det eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QkDetExpand.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QkDetExpand.lean#L9-L20

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_eval {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (hdeg : ∀ i, (p i).natDegree ≤ i) :
    (Matrix.of fun i j => (p j).eval (v i)).det = (Matrix.vandermonde v).det * ∏ i, (p i).coeff i := by sorry
