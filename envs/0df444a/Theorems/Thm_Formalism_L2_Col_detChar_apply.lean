-- Prove2me | Theorems.Thm_Formalism_L2_Col_detChar_apply
-- name    : Formalism.L2.Col.detChar_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:03.017817+00:00
-- url     : https://prove2.me/theorems/3225b2f5-9c37-4162-b102-6118c0c79fe9
-- title:
--   Col: det Char apply
-- statement:
--   The Col construction uses the det Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L244-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L244-L246

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

theorem Formalism.L2.Col.detChar_apply (χ : ℕ → κˣ →* Kˣ) (a : ℕ) (bl : List ℕ) (M : ↥(blockUT n κ a bl)) :
    detChar χ n a bl M = ∏ s ∈ Finset.range bl.length, χ s (blkDet n κ (coarse a bl) (s + 1) M) := by sorry
