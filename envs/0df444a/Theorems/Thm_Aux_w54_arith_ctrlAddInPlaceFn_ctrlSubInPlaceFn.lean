-- Prove2me | Theorems.Thm_Aux_w54_arith_ctrlAddInPlaceFn_ctrlSubInPlaceFn
-- name    : Aux_w54_arith.ctrlAddInPlaceFn_ctrlSubInPlaceFn
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:31.244108+00:00
-- url     : https://prove2.me/theorems/4127bf09-292a-5dda-86b6-46672bc06f2f
-- title:
--   Controlled variable-register arithmetic functions are inverse
-- statement:
--   For natural w, let A(c,a,b)=(c,a,b+ca mod 2^w) and S(c,a,b)=(c,a,b−ca mod 2^w), with a,b unsigned w-bit registers and c Boolean. For every basis string x, $$A(S(x))=x,\qquad S(A(x))=x.$$
-- source:
--   Reused accepted arithmetic proof by Robin Kothari, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0). Exact local formalization: Solutions/Section5LcgArithmeticFoundation.lean, lines 2286–2288; attribution is recorded in the file header. This copied foundation supports Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3; it is not a new contribution.

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
import Theorems.Thm_Aux_w54_arith_addInPlaceFn_subInPlaceFn
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

theorem Aux_w54_arith.ctrlAddInPlaceFn_ctrlSubInPlaceFn (w : ℕ) (x : Qubits (1 + w + w)) :
    Aux_w54_arith.ctrlAddInPlaceFn w (Aux_w54_arith.ctrlSubInPlaceFn w x) = x ∧
      Aux_w54_arith.ctrlSubInPlaceFn w (Aux_w54_arith.ctrlAddInPlaceFn w x) = x := by sorry
