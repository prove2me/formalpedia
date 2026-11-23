-- Prove2me | Theorems.Thm_Formalism_L2_Col_mem_btG
-- name    : Formalism.L2.Col.mem_btG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:26.981093+00:00
-- url     : https://prove2.me/theorems/d42cd814-5512-4334-9d66-5b942daf43b7
-- title:
--   Col: mem bt G
-- statement:
--   The Col construction uses the mem bt G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L103-L105

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

theorem Formalism.L2.Col.mem_btG {β : ℕ → ℕ} {M : GL (Fin n) κ} :
    M ∈ btG n κ β ↔ ∀ i j : Fin n, β j.val < β i.val → (M : Matrix (Fin n) (Fin n) κ) i j = 0 := by sorry
