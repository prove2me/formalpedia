-- Prove2me | Theorems.Thm_Aux_w54_arith_bitsToNatLSB_add_two_pow_rev
-- name    : Aux_w54_arith.bitsToNatLSB_add_two_pow_rev
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:15.08817+00:00
-- url     : https://prove2.me/theorems/2ae9ce27-956a-5834-8d7f-2715be0f7cf4
-- title:
--   Values of complementary bit strings sum to the all-ones value
-- statement:
--   For a natural number $w$ and any $w$-bit string $x$, let $\overline{x}$ be its bitwise Boolean complement and let $\operatorname{val}$ denote least-significant-bit-first interpretation. Then
--
--   $$
--   \operatorname{val}(\overline{x})+\operatorname{val}(x)=2^w-1.
--   $$
--
--   This identity relates bitwise complementation to integer arithmetic, including the empty register.
-- source:
--   Reused arithmetic result by Robin Kothari, accepted Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353, Apache-2.0; attribution in Solutions/Section5LcgArithmeticFoundation.lean, lines 15–17. Exact local source: Solutions/Section5LcgArithmeticFoundation.lean, Aux_w54_arith.bitsToNatLSB_add_two_pow_rev, lines 122–145.

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
import Mathlib
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

theorem Aux_w54_arith.bitsToNatLSB_add_two_pow_rev (w : ℕ) (x : Qubits w) :
    bitsToNatLSB (fun i => !x i) + bitsToNatLSB x = 2 ^ w - 1 := by sorry
