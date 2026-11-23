-- Prove2me | Theorems.Thm_Formalism_L2_Col_blockZero_val
-- name    : Formalism.L2.Col.blockZero_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:23.573202+00:00
-- url     : https://prove2.me/theorems/765909db-5ee6-475c-9f3d-4cd3c6914698
-- title:
--   Col: block Zero val
-- statement:
--   The Col construction uses the block Zero val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L404-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L404-L405

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ]
variable {K : Type} [Field K]

theorem Formalism.L2.Col.blockZero_val {r : ℕ} (h : r ≤ n) (bl : List ℕ) (M : ↥(blockUT n κ r bl)) :
    (blk0 n κ h bl M : Matrix (Fin r) (Fin r) κ) = restr h (M.1 : Matrix (Fin n) (Fin n) κ) := by sorry
