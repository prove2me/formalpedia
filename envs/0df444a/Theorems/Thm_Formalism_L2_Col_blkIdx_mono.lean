-- Prove2me | Theorems.Thm_Formalism_L2_Col_blkIdx_mono
-- name    : Formalism.L2.Col.blkIdx_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:02.878813+00:00
-- url     : https://prove2.me/theorems/ea8a759a-f67e-425a-8802-6c61f029fde6
-- title:
--   Col: blk Idx mono
-- statement:
--   The Col construction uses the blk Idx mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L57-L67

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

theorem Formalism.L2.Col.blkIdx_mono (bl : List ℕ) : Monotone (blkIdx bl) := by sorry
