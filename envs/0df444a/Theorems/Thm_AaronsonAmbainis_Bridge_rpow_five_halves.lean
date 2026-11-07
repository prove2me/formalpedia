-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rpow_five_halves
-- name    : AaronsonAmbainis.Bridge.rpow_five_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:12:54.770986+00:00
-- url     : https://prove2.me/theorems/989b24ea-73fc-49e1-8f4c-9b3b72b4e8f4
-- title:
--   Bridge: rpow five halves
-- statement:
--   The real power `ε^{5/2}` is `ε² √ε`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L378-L380
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L378-L380

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.rpow_five_halves {ε : ℝ} (hε : 0 ≤ ε) : ε ^ ((5 : ℝ) / 2) = ε ^ 2 * Real.sqrt ε := by sorry
