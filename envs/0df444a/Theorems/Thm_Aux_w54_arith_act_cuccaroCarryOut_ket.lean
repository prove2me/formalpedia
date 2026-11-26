-- Prove2me | Theorems.Thm_Aux_w54_arith_act_cuccaroCarryOut_ket
-- name    : Aux_w54_arith.act_cuccaroCarryOut_ket
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:42:57.611555+00:00
-- url     : https://prove2.me/theorems/a21266bc-7742-50f4-a101-f16aaf661ff0
-- title:
--   Cuccaro carry-out circuit computes overflow and restores its inputs
-- statement:
--   Let $w\ge0$ and let $a,b$ be $w$-bit strings interpreted in least-significant-bit-first order, with values $A,B$. Let $c,t\in\{0,1\}$ be a carry input and target bit. Place these bits in the order $(c,a_0,b_0,\ldots,a_{w-1},b_{w-1},t)$. The Cuccaro carry-out circuit acts on the corresponding computational basis state by
--
--   $$
--   |c,a,b,t\rangle\longmapsto|c,a,b,t\mathbin{\oplus}\mathbf1_{A+B+c\ge2^w}\rangle.
--   $$
--
--   This specifies reversible overflow extraction while preserving both operands and the carry input.
-- source:
--   Reused arithmetic result by Robin Kothari, accepted Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353, Apache-2.0; attribution in Solutions/Section5LcgArithmeticFoundation.lean, lines 15–17. Exact local source: Solutions/Section5LcgArithmeticFoundation.lean, Aux_w54_arith.act_cuccaroCarryOut_ket, lines 1554–1721.

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

theorem Aux_w54_arith.act_cuccaroCarryOut_ket (w : ℕ) (cin tgt : Bool) (a b : Qubits w) :
    let init : Qubits (1 + 2 * w + 1) := fun u =>
      if h0 : u.1 = 0 then cin
      else if ht : u.1 = 1 + 2 * w then tgt
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    let carryBit := decide (2 ^ w ≤ bitsToNatLSB a + bitsToNatLSB b + (if cin then 1 else 0))
    let out : Qubits (1 + 2 * w + 1) := Function.update init ⟨1 + 2 * w, by omega⟩ (xor tgt carryBit)
    act (Aux_w54_arith.cuccaroCarryOut w).unitary (ket init) = ket out := by sorry
