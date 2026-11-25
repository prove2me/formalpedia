-- Prove2me | Theorems.Thm_DetDLP_m89_s1_fp_plan_prepare
-- name    : DetDLP.m89_s1_fp_plan_prepare
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:34:54.003343+00:00
-- url     : https://prove2.me/theorems/b401aca1-4ff4-4608-88e2-e191c47555b3
-- title:
--   Select and serialize the multiplicative group seed
-- statement:
--   Given exact prefix-moment counts, compute the full-group marker or the threshold and winning seed. Two fixed preprocessing machines, on the enumeration input and the target input respectively, append the same plan to the original word. Both use polynomial visited space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_DetDLP_M89_S1_Plans
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_fp_plan_prepare : CountOracle → ∃ (U : PrimitiveMachine) (u : Fin U.tapeCount) (V : PrimitiveMachine) (v : Fin V.tapeCount) (J : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 
      let b := bitLen p; let m := blockCount b
      ∃ L : Option (ℕ × FpSeed p m), m89_fp_plan_ok L ∧
        RunsWithin U u (countWord p) (Encoding.encodeList id [(countWord p),m89_fp_plan_word L]) (mainSpaceBound J b) (polyBound J b) ∧
        ∀ X : (ZMod p)ˣ, RunsWithin V v (encodeNatListBin [p,(X : ZMod p).val]) (Encoding.encodeList id [(encodeNatListBin [p,(X : ZMod p).val]),m89_fp_plan_word L]) (mainSpaceBound J b) (polyBound J b) := by sorry
