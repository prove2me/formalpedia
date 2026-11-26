-- Prove2me | Theorems.Thm_Aux_w54_arith_ltRegCircuit_implements
-- name    : Aux_w54_arith.ltRegCircuit_implements
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:56.253797+00:00
-- url     : https://prove2.me/theorems/1a0add33-6e69-51c4-8967-9ebfac74073b
-- title:
--   Correctness of the clean unsigned register comparator
-- statement:
--   For every natural w, the source's strict register-comparison circuit on two unsigned w-bit registers, target t and one ancillary wire implements the less-than predicate and restores the ancilla: $$U_C|a,b,t,0⟩=|a,b,t\mathbin{\mathrm{xor}}[a<b],0⟩.$$
-- source:
--   Reused accepted arithmetic proof by Robin Kothari, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0). Exact local formalization: Solutions/Section5LcgArithmeticFoundation.lean, lines 1794–1795; attribution is recorded in the file header. This copied foundation supports Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3; it is not a new contribution.

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
import Theorems.Thm_Aux_w54_arith_act_cuccaroCarryOut_ket
import Theorems.Thm_Aux_w54_arith_bitsToNatLSB_add_two_pow_rev
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

theorem Aux_w54_arith.ltRegCircuit_implements (w : ℕ) :
    (Aux_w54_arith.ltRegCircuit w).ImplementsOnClean (permMat (Aux_w54_arith.ltRegFn w)) := by sorry
