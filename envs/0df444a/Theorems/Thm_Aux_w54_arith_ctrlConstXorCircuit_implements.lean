-- Prove2me | Theorems.Thm_Aux_w54_arith_ctrlConstXorCircuit_implements
-- name    : Aux_w54_arith.ctrlConstXorCircuit_implements
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:53.763578+00:00
-- url     : https://prove2.me/theorems/dc79fe3e-a374-58d7-b285-713dd0d1ba83
-- title:
--   Clean controlled XOR with a constant bit string
-- statement:
--   Let $w,c$ be natural numbers, $u$ a Boolean control, and $x$ a $w$-bit register. Let $c^{(w)}$ be the $w$ low bits of $c$ in least-significant-bit-first order. With zero-initialized auxiliary wires, the controlled constant-XOR circuit implements
--
--   $$
--   |u,x,0_{\mathrm{anc}}\rangle\longmapsto|u,x\mathbin{\oplus}(u\,c^{(w)}),0_{\mathrm{anc}}\rangle.
--   $$
--
--   The control is preserved, and the bit mask is applied exactly when that control is true.
-- source:
--   Reused arithmetic result by Robin Kothari, accepted Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353, Apache-2.0; attribution in Solutions/Section5LcgArithmeticFoundation.lean, lines 15–17. Exact local source: Solutions/Section5LcgArithmeticFoundation.lean, Aux_w54_arith.ctrlConstXorCircuit_implements, lines 622–643.

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

theorem Aux_w54_arith.ctrlConstXorCircuit_implements (w c : ℕ) :
    (Aux_w54_arith.ctrlConstXorCircuit w c).ImplementsOnClean (permMat (Aux_w54_arith.ctrlConstXorFn w c)) := by sorry
