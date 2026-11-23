-- Prove2me | Theorems.Thm_Formalism_L2_Col_blkDet_val
-- name    : Formalism.L2.Col.blkDet_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:05.369908+00:00
-- url     : https://prove2.me/theorems/5d204533-3161-4fe1-8f8e-b30d4b249644
-- title:
--   Col: blk Det val
-- statement:
--   The Col construction uses the blk Det val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L138-L139

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

theorem Formalism.L2.Col.blkDet_val {β : ℕ → ℕ} (c : ℕ) (M : ↥(btG n κ β)) :
    ((blkDet n κ β c M : κˣ) : κ) = ((M.1 : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => β i.val) c).det := by sorry
