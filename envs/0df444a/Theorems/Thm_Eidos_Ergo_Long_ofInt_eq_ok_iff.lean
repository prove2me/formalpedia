-- Prove2me | Theorems.Thm_Eidos_Ergo_Long_ofInt_eq_ok_iff
-- name    : Eidos.Ergo.Long.ofInt_eq_ok_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:06.734489+00:00
-- url     : https://prove2.me/theorems/c71093b3-6745-48b3-a04e-c0220c6d8071
-- title:
--   Long: of Int eq ok iff
-- statement:
--   The Long construction uses the of Int eq ok iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Long.lean#L27-L37
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Long.lean#L27-L37

import Std
import Definitions.Def_Eidos_Ergo_Long
set_option autoImplicit false
open Eidos Eidos.Ergo
open Eidos.Ergo.Long

theorem Eidos.Ergo.Long.ofInt_eq_ok_iff (n : Int) (x : Long) :
    ofInt n = .ok x ↔ n = x.val := by sorry
