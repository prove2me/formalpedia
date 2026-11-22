-- Prove2me | Theorems.Thm_Formalism_REAL_exp_conjTranspose_of_hermitian
-- name    : Formalism.REAL.exp_conjTranspose_of_hermitian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:52:02.009145+00:00
-- url     : https://prove2.me/theorems/57ba9655-011a-48ec-9178-d4ab06223a44
-- title:
--   REAL: exp conj Transpose of hermitian
-- statement:
--   The REAL construction uses the exp conj Transpose of hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L38-L40

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}

theorem Formalism.REAL.exp_conjTranspose_of_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) :
    (NormedSpace.exp A)ᴴ = NormedSpace.exp A := by sorry
