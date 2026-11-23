-- Prove2me | Theorems.Thm_Formalism_L2_Col_diagEmb_injective
-- name    : Formalism.L2.Col.diagEmb_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:37.101825+00:00
-- url     : https://prove2.me/theorems/97b1af98-187d-44c3-af22-cc972882de3e
-- title:
--   Col: diag Emb injective
-- statement:
--   The Col construction uses the diag Emb injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L301-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L301-L311

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

theorem Formalism.L2.Col.diagEmb_injective {r : ℕ} (h : r ≤ n) : Function.Injective (diagEmb κ h) := by sorry
