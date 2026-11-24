-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_Mpi_eq_image
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_Mpi_eq_image
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:58:45.732771+00:00
-- url     : https://prove2.me/theorems/c1dfd8dc-335f-4e7a-af0b-51f3a729efc3
-- title:
--   Column Families: qb Mpi eq image
-- statement:
--   The Column Families construction uses the qb Mpi eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L68-L77

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
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
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_Mpi_eq_image (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi) :
    CF.Mpi pi = Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}) := by sorry
