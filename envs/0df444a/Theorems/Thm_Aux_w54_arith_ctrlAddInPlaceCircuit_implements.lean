-- Prove2me | Theorems.Thm_Aux_w54_arith_ctrlAddInPlaceCircuit_implements
-- name    : Aux_w54_arith.ctrlAddInPlaceCircuit_implements
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:08.654552+00:00
-- url     : https://prove2.me/theorems/b4dce3b0-68b9-5ed3-a13e-386ef9340f0c
-- title:
--   Correctness of the clean controlled variable-register adder
-- statement:
--   For every natural w, the source's controlled in-place adder circuit on a control, two w-bit registers and w+1 ancillary wires implements controlled modular addition and returns clean ancillas to zero: $$U_C|c,a,b,0^{w+1}⟩=|c,a,b+ca\bmod2^w,0^{w+1}⟩.$$
-- source:
--   Reused accepted arithmetic proof by Robin Kothari, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0). Exact local formalization: Solutions/Section5LcgArithmeticFoundation.lean, lines 2092–2093; attribution is recorded in the file header. This copied foundation supports Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3; it is not a new contribution.

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
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

theorem Aux_w54_arith.ctrlAddInPlaceCircuit_implements (w : ℕ) :
    (Aux_w54_arith.ctrlAddInPlaceCircuit w).ImplementsOnClean (permMat (Aux_w54_arith.ctrlAddInPlaceFn w)) := by sorry
