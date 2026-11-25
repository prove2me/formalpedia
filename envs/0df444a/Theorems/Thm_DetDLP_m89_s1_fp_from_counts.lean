-- Prove2me | Theorems.Thm_DetDLP_m89_s1_fp_from_counts
-- name    : DetDLP.m89_s1_fp_from_counts
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T20:22:37.714249+00:00
-- url     : https://prove2.me/theorems/6a864bc0-729b-42d8-a44c-61f057e27cbc
-- title:
--   Prime-field Stage I machines from exact prefix counts
-- statement:
--   Given a uniform exact Stage I counting machine, there exist fixed deterministic enumeration and decoding machines and a common constant for every prime $p$, including $2$. The enumerator returns duplicate-free blocks: the entire unit group in the small regime, and the blocks of a seed from the winning full prefix otherwise. On input the prime and target alone, where the target admits a product using two entries in each block, the decoder outputs such a decomposition. Enumeration respects the Stage I time and space bounds, and decoding respects the same time bound in polynomial space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 Proof of Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_fp_from_counts :
    CountOracle →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
       (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          fpBase (fun i => (F i).toFinset) ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C b) (mainSpaceBound C b) ∧
          ∀ X : (ZMod p)ˣ,
            (∃ A B : Fin m → (ZMod p)ˣ,
              (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
              (∏ i : Fin m, (A i * B i)) = X) →
            ∃ A B : Fin m → (ZMod p)ˣ,
              (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
              (∏ i : Fin m, (A i * B i)) = X ∧
              RunsWithin M_dec out_dec
                (encodeNatListBin [p, (X : ZMod p).val])
                (encodeFpDecomp A B)
                (mainSpaceBound C b) (polyBound C b)) := by sorry
