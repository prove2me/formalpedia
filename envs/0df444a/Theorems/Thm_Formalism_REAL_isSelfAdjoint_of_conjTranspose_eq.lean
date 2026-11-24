-- Prove2me | Theorems.Thm_Formalism_REAL_isSelfAdjoint_of_conjTranspose_eq
-- name    : Formalism.REAL.isSelfAdjoint_of_conjTranspose_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:15.105584+00:00
-- url     : https://prove2.me/theorems/4ad92c01-a0c4-4680-9f9a-1c8f20f0b6d5
-- title:
--   REAL: is Self Adjoint of conj Transpose eq
-- statement:
--   The REAL construction uses the is Self Adjoint of conj Transpose eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L28-L29

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

theorem Formalism.REAL.isSelfAdjoint_of_conjTranspose_eq {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) : IsSelfAdjoint A := by sorry
