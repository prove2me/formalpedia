-- Prove2me | Theorems.Thm_Aux_w54_arith_cswapRegCircuit_implements
-- name    : Aux_w54_arith.cswapRegCircuit_implements
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:59.057435+00:00
-- url     : https://prove2.me/theorems/14700d01-edd2-41ad-b3aa-8af456ea4eca
-- title:
--   Correctness of the controlled register-swap foundation
-- statement:
--   For every natural width w, the source's register-swap circuit on one control and two w-bit registers implements the basis permutation that swaps the registers exactly when the control is one, with no ancillas: $$U_C|c,a,b⟩=\begin{cases}|c,b,a⟩&c=1,\\|c,a,b⟩&c=0.\end{cases}$$
-- source:
--   Reused accepted arithmetic proof by Robin Kothari, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0). Exact local formalization: Solutions/Section5LcgArithmeticFoundation.lean, lines 444–445; attribution is recorded in the file header. This copied foundation supports Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3; it is not a new contribution.

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

theorem Aux_w54_arith.cswapRegCircuit_implements (w : ℕ) :
    (Aux_w54_arith.cswapRegCircuit w).ImplementsOnClean (permMat (cswapRegFn w)) := by sorry
