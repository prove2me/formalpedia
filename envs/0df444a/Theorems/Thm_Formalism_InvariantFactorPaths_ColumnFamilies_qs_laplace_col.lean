-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_laplace_col
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:03.498196+00:00
-- url     : https://prove2.me/theorems/10aafc66-677d-4258-b8dd-97c84dd2f2ed
-- title:
--   Column Families: qs laplace col
-- statement:
--   The Column Families construction uses the qs laplace col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L119-L123

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace_col (A I : Finset (Fin n)) (m : Fin n) :
    ∑ k ∈ A, ((qs_sg (A.erase k) k : ℤ) : R) * qs_mn g (A.erase k) I * g k m =
      if m ∈ I then 0 else ((qs_sg I m : ℤ) : R) * qs_mn g A (insert m I) := by sorry
