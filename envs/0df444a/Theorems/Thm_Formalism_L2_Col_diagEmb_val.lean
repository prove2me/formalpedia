-- Prove2me | Theorems.Thm_Formalism_L2_Col_diagEmb_val
-- name    : Formalism.L2.Col.diagEmb_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:47.438986+00:00
-- url     : https://prove2.me/theorems/4612d5bd-6169-4728-b239-f1a9dc81985c
-- title:
--   Col: diag Emb val
-- statement:
--   The Col construction uses the diag Emb val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L298-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L298-L299

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

theorem Formalism.L2.Col.diagEmb_val {r : ℕ} (h : r ≤ n) (g : GL (Fin r) κ) :
    (diagEmb κ h g : Matrix (Fin n) (Fin n) κ) = diagMat r n (g : Matrix (Fin r) (Fin r) κ) := by sorry
