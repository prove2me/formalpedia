-- Prove2me | Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_colGenJ
-- name    : Formalism.NG.ColumnGeneratorDecomposition.map_colGenJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:46.854077+00:00
-- url     : https://prove2.me/theorems/31b80226-5ba3-40fb-8738-f813e1dfa032
-- title:
--   Column Generator Decomposition: map col Gen J
-- statement:
--   The Column Generator Decomposition construction uses the map col Gen J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L48-L53

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

theorem Formalism.NG.ColumnGeneratorDecomposition.map_colGenJ (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (y : Ymod r χ E) (l : ι) (c : A)
    (s : Fin (j l) → A) (c₀ : A) :
    ψ (colGenJ y l c s c₀) = ψ (y, 0) + c • ψ (fNu l) + ∑ a, s a • ψ (fSig l a) +
      c₀ • ψ (fSig0 l) := by sorry
