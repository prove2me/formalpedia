-- Prove2me | Theorems.Thm_FPP_Carmichael_not_isPrimePow
-- name    : FPP.Carmichael.not_isPrimePow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:56.516119+00:00
-- url     : https://prove2.me/theorems/a06a3195-1c97-4f29-80ae-e642a1de53e0
-- title:
--   Carmichael: not is Prime Pow
-- statement:
--   The Carmichael construction uses the not is Prime Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L167-L171
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L167-L171

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
set_option autoImplicit false
open Nat
open FPP
open FPP.Carmichael
variable {n : ℕ}

theorem FPP.Carmichael.not_isPrimePow [Fact (1 < n)] (hc : Carmichael n) (hnp : ¬n.Prime) :
    ¬IsPrimePow n := by sorry
