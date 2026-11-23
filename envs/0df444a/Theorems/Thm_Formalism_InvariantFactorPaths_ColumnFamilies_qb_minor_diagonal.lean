-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_minor_diagonal
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_minor_diagonal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:01.614686+00:00
-- url     : https://prove2.me/theorems/471face8-d399-4b85-8dec-247caced7944
-- title:
--   Column Families: qb minor diagonal
-- statement:
--   The Column Families construction uses the qb minor diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L37-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L37-L65

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
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
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_minor_diagonal {R : Type} [CommRing R] (d : Fin n → R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    Matrix.det (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) =
      if J = I then ∏ x ∈ J, d x else 0 := by sorry
