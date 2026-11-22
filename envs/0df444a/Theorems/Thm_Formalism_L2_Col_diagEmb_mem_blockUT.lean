-- Prove2me | Theorems.Thm_Formalism_L2_Col_diagEmb_mem_blockUT
-- name    : Formalism.L2.Col.diagEmb_mem_blockUT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:23.916781+00:00
-- url     : https://prove2.me/theorems/3997f73e-9aaf-4925-8392-f91eb179e36a
-- title:
--   Col: diag Emb mem block UT
-- statement:
--   The Col construction uses the diag Emb mem block UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L313-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L313-L318

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

theorem Formalism.L2.Col.diagEmb_mem_blockUT {r : ℕ} (h : r ≤ n) (bl : List ℕ) (g : GL (Fin r) κ) : diagEmb κ h g ∈ blockUT n κ r bl := by sorry
