-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_laplace_inv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:47.949702+00:00
-- url     : https://prove2.me/theorems/e2b1c200-7262-40ce-bff5-5c60d88db9ed
-- title:
--   Column Families: qs laplace inv
-- statement:
--   The Column Families construction uses the qs laplace inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L99-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L99-L117

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
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
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace_inv (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (J K : Finset (Fin n)) (a : Fin n) :
    ∑ m, (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) * g' m a else 0) =
      if a ∈ J then ((qs_sg (J.erase a) a : ℤ) : R) * qs_mn g (J.erase a) K else 0 := by sorry
