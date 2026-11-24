-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_det_expand
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:38.879977+00:00
-- url     : https://prove2.me/theorems/20b3a6f4-3313-4507-99e6-f2c40b633386
-- title:
--   Column Families: qk det expand
-- statement:
--   The Column Families construction uses the qk det expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QkDetExpand.lean#L50-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QkDetExpand.lean#L50-L76

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_expand {R : Type*} [CommRing R] {n : ℕ} (v w : Fin n → R) (x : R) :
    (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * w i ^ (j : ℕ)).det =
      ∑ s : Finset (Fin n), x ^ s.card * (Matrix.vandermonde (s.piecewise w v)).det := by sorry
