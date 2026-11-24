-- Prove2me | Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_sigRel
-- name    : Formalism.NG.ColumnGeneratorDecomposition.map_sigRel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:46.36198+00:00
-- url     : https://prove2.me/theorems/2ac050a9-8072-4af1-a694-1779e682ab04
-- title:
--   Column Generator Decomposition: map sig Rel
-- statement:
--   The Column Generator Decomposition construction uses the map sig Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L55-L59

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.ColumnGeneratorDecomposition
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
variable {M : Type*} [AddCommGroup M] [Module A M]

theorem Formalism.NG.ColumnGeneratorDecomposition.map_sigRel (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (l : ι) (a : Fin (j l)) (t : A) :
    ψ (colGenJ 0 l 0 (Pi.single a t) 0) = t • ψ (fSig l a) := by sorry
