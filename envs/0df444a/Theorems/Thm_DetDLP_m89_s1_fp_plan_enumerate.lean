-- Prove2me | Theorems.Thm_DetDLP_m89_s1_fp_plan_enumerate
-- name    : DetDLP.m89_s1_fp_plan_enumerate
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:35:14.079409+00:00
-- url     : https://prove2.me/theorems/080606f7-2a85-4d98-85da-d2f706bf7daf
-- title:
--   Enumerate blocks from a supplied multiplicative group plan
-- statement:
--   Given a valid plan on the input tape and an exact count oracle, output each block without duplicates, with the prescribed set of elements. The large branch uses the element-prefix queries; the small branch enumerates the full group. No seed selection or target decomposition is required.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_DetDLP_M89_S1_Plans
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_fp_plan_enumerate : CountOracle → ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 
      let b := bitLen p; let m := blockCount b
      ∀ L : Option (ℕ × FpSeed p m), m89_fp_plan_ok L → ∃ F : Fin m → List (ZMod p)ˣ,
        (∀ i, (F i).Nodup ∧ (F i).toFinset = m89_fp_plan_block L i) ∧
        RunsWithin M o (Encoding.encodeList id [(countWord p),m89_fp_plan_word L]) (encodeFpFactorBlocks F) (mainSpaceBound K b) (mainSpaceBound K b) := by sorry
