-- Prove2me | Theorems.Thm_Aux_w54_arith_addInPlaceCircuit_implements
-- name    : Aux_w54_arith.addInPlaceCircuit_implements
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:14.102958+00:00
-- url     : https://prove2.me/theorems/6de0206b-b35c-5da1-bb5f-5a63e2443d55
-- title:
--   Clean implementation of modular in-place addition
-- statement:
--   Let $w$ be a natural number and let $a,b$ be two $w$-bit registers, interpreted in least-significant-bit-first order with values $A,B$. With all auxiliary wires initialized to zero, the in-place addition circuit implements
--
--   $$
--   |a,b,0_{\mathrm{anc}}\rangle\longmapsto|a,(A+B)\bmod2^w,0_{\mathrm{anc}}\rangle.
--   $$
--
--   The equality specifies the induced permutation matrix on the main registers and restoration of every auxiliary wire.
-- source:
--   Reused arithmetic result by Robin Kothari, accepted Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353, Apache-2.0; attribution in Solutions/Section5LcgArithmeticFoundation.lean, lines 15–17. Exact local source: Solutions/Section5LcgArithmeticFoundation.lean, Aux_w54_arith.addInPlaceCircuit_implements, lines 1383–1442.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Mathlib
import Theorems.Thm_Aux_w54_arith_act_cuccaroCore_ket
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

theorem Aux_w54_arith.addInPlaceCircuit_implements (w : ℕ) :
    (Aux_w54_arith.addInPlaceCircuit w).ImplementsOnClean (permMat (Aux_w54_arith.addInPlaceFn w)) := by sorry
