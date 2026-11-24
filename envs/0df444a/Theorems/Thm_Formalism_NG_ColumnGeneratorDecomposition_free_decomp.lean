-- Prove2me | Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_free_decomp
-- name    : Formalism.NG.ColumnGeneratorDecomposition.free_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:08.418622+00:00
-- url     : https://prove2.me/theorems/54677ac8-c5f8-4dd5-9309-7bb6bcf17bfc
-- title:
--   Column Generator Decomposition: free decomp
-- statement:
--   The Column Generator Decomposition construction uses the free decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L38-L44

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

theorem Formalism.NG.ColumnGeneratorDecomposition.free_decomp [Fintype ι] (z : ColFreeJ A r χ E ι j) :
    z = ((z.1, 0) : ColFreeJ A r χ E ι j) +
      ∑ l, colGenJ 0 l (z.2 l).1 (z.2 l).2.1 (z.2 l).2.2 := by sorry
