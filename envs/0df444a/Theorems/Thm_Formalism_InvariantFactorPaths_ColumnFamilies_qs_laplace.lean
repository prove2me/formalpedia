-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_laplace
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:57.613833+00:00
-- url     : https://prove2.me/theorems/99d8ccfe-e0b4-4270-b19e-6c00cd3ddb42
-- title:
--   Column Families: qs laplace
-- statement:
--   The Column Families construction uses the qs laplace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L85-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L85-L117

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
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
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace (A I : Finset (Fin n)) (k : Fin n) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g k m =
      if k ∈ A then 0 else ((qs_sg A k : ℤ) : R) * qs_mn g (insert k A) I := by sorry
