-- Prove2me | Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_colGenJ_decomp
-- name    : Formalism.NG.ColumnGeneratorDecomposition.colGenJ_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:36.513303+00:00
-- url     : https://prove2.me/theorems/8ee03ff8-3bf9-41a0-bbd9-d96464adc09c
-- title:
--   Column Generator Decomposition: col Gen J decomp
-- statement:
--   The Column Generator Decomposition construction uses the col Gen J decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L23-L36

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

theorem Formalism.NG.ColumnGeneratorDecomposition.colGenJ_decomp (y : Ymod r χ E) (l : ι) (c : A) (s : Fin (j l) → A) (c₀ : A) :
    colGenJ y l c s c₀ = ((y, 0) : ColFreeJ A r χ E ι j) + c • fNu l +
      ∑ a, s a • fSig l a + c₀ • fSig0 l := by sorry
