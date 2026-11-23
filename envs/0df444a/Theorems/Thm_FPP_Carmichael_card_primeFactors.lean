-- Prove2me | Theorems.Thm_FPP_Carmichael_card_primeFactors
-- name    : FPP.Carmichael.card_primeFactors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:00:45.654974+00:00
-- url     : https://prove2.me/theorems/3ec22875-7c12-43ce-b85b-3636cbdfc8c3
-- title:
--   Carmichael: card prime Factors
-- statement:
--   This is (ii) of Thm. 5 of [conrad2016carmichael].
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L133-L165
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L133-L165

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

theorem FPP.Carmichael.card_primeFactors [hn : Fact (1 < n)] (hc : Carmichael n) (hnp : ¬n.Prime) :
    3 ≤ n.primeFactors.card := by sorry
