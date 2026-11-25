-- Prove2me | Theorems.Thm_DetDLP_m89_flatten_factor_blocks_machine
-- name    : DetDLP.m89_flatten_factor_blocks_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T17:12:54.808874+00:00
-- url     : https://prove2.me/theorems/f6ef7e21-ac14-4176-a70b-0a75e8a5251e
-- title:
--   Order-preserving flattening of encoded factor-base blocks
-- statement:
--   One fixed two-tape machine converts a list of encoded residue blocks into the encoded list of all residues in their original order. For input length $L$, its running time is at most $49L+63$ and every prefix of the run visits at most $18L+48$ cells.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3, Section 3.3 (ordered factor-base scan).

import Definitions.Def_DetDLP_FactorBase
set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.m89_flatten_factor_blocks_machine :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount), ∀ (p : ℕ) [NeZero p] {m : ℕ} (F : Fin m → List (ZMod p)ˣ),
     let input := encodeFpFactorBlocks F
    let output := encodeNatListBin ((List.ofFn F).flatten.map (fun a : (ZMod p)ˣ => (a : ZMod p).val))
    RunsWithin M out input output
      ((49*input.length+63 : ℕ) : ℝ) ((18*input.length+48 : ℕ) : ℝ) := by sorry
