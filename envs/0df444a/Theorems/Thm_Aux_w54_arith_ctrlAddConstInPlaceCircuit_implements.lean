-- Prove2me | Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceCircuit_implements
-- name    : Aux_w54_arith.ctrlAddConstInPlaceCircuit_implements
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:30.049745+00:00
-- url     : https://prove2.me/theorems/c7f31b08-be0f-4324-838f-9d0567caeb24
-- title:
--   Clean controlled addition of a constant modulo a power of two
-- statement:
--   Let $w,c$ be natural numbers, $u$ a Boolean control, and $b$ a $w$-bit register of least-significant-bit-first value $B$. With all auxiliary wires initially zero, the controlled constant-adder implements
--
--   $$
--   |u,b,0_{\mathrm{anc}}\rangle\longmapsto|u,(B+uc)\bmod2^w,0_{\mathrm{anc}}\rangle,
--   $$
--
--   where $u$ is interpreted as $0$ or $1$.
--
--   This gives the exact permutation implemented on the main register while restoring its clean workspace.
-- source:
--   Reused arithmetic result by Robin Kothari, accepted Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353, Apache-2.0; attribution in Solutions/Section5LcgArithmeticFoundation.lean, lines 15–17. Exact local source: Solutions/Section5LcgArithmeticFoundation.lean, Aux_w54_arith.ctrlAddConstInPlaceCircuit_implements, lines 2450–2624.

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
import Theorems.Thm_Aux_w54_arith_addInPlaceCircuit_implements
import Theorems.Thm_Aux_w54_arith_ctrlConstXorCircuit_implements
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

theorem Aux_w54_arith.ctrlAddConstInPlaceCircuit_implements (w c : ℕ) :
    (Aux_w54_arith.ctrlAddConstInPlaceCircuit w c).ImplementsOnClean (permMat (Aux_w54_arith.ctrlAddConstInPlaceFn w c)) := by sorry
