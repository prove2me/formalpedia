-- Prove2me | Theorems.Thm_Formalism_L2_Col_HK_le_uniUT
-- name    : Formalism.L2.Col.HK_le_uniUT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:26.056528+00:00
-- url     : https://prove2.me/theorems/3ffbeddf-e210-482e-bd0d-adbf25fafe08
-- title:
--   Col: HK le uni UT
-- statement:
--   The Col construction uses the HK le uni UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L358-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L358-L364

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

theorem Formalism.L2.Col.HK_le_uniUT (n : ℕ) (κ : Type) [CommRing κ] (r : ℕ) (bl : List ℕ) : HK n κ r bl ≤ uniUT n κ r bl := by sorry
