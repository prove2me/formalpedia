-- Prove2me | Theorems.Thm_Aux_w54_arith_act_cuccaroCore_ket
-- name    : Aux_w54_arith.act_cuccaroCore_ket
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:07.992255+00:00
-- url     : https://prove2.me/theorems/87a15750-ad82-4d3c-94b6-556404a8423a
-- title:
--   Cuccaro core performs addition with a carry input
-- statement:
--   For $w\ge0$, let $a,b$ be $w$-bit strings of values $A,B$ in least-significant-bit-first order, and let $c$ be a Boolean carry input. Interleave their wires as $(c,a_0,b_0,\ldots,a_{w-1},b_{w-1})$. Writing $s$ for the $w$ low bits of $A+B+c$, the Cuccaro core satisfies
--
--   $$
--   U_{\mathrm{core}}|c,a,b\rangle=|c,a,s\rangle,\qquad \operatorname{value}(s)=(A+B+c)\bmod2^w.
--   $$
--
--   This is the computational basis specification of the addition core.
-- source:
--   Reused arithmetic result by Robin Kothari, accepted Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353, Apache-2.0; attribution in Solutions/Section5LcgArithmeticFoundation.lean, lines 15–17. Exact local source: Solutions/Section5LcgArithmeticFoundation.lean, Aux_w54_arith.act_cuccaroCore_ket, lines 1130–1348.

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
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

theorem Aux_w54_arith.act_cuccaroCore_ket (w : ℕ) (cin : Bool) (a b : Qubits w) :
    let init : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    let sNat := bitsToNatLSB a + bitsToNatLSB b + (if cin then 1 else 0)
    let sout := natToBitsLSB w sNat
    let out : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else sout ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    act (Aux_w54_arith.cuccaroCore w).unitary (ket init) = ket out := by sorry
