-- Prove2me | Theorems.Thm_Formalism_L2_Col_supChar_val
-- name    : Formalism.L2.Col.supChar_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:32.701838+00:00
-- url     : https://prove2.me/theorems/77d010e8-5407-4788-8dd7-95ed194c33d8
-- title:
--   Col: sup Char val
-- statement:
--   The Col construction uses the sup Char val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L238-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L238-L239

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

theorem Formalism.L2.Col.supChar_val (ψ : AddChar κ K) (a : ℕ) (bl : List ℕ) (S : Finset ℕ) (M : ↥(uniUT n κ a bl)) :
    ((supChar ψ n a bl S M : Kˣ) : K) = ψ (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ)) := by sorry
