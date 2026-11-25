-- Prove2me | Theorems.Thm_DetDLP_m89_s1_ec_from_counts
-- name    : DetDLP.m89_s1_ec_from_counts
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T20:22:33.148462+00:00
-- url     : https://prove2.me/theorems/15bc2bc9-bdc0-4a9c-96f2-aaec18cdd61a
-- title:
--   Elliptic-curve Stage I machines from exact prefix counts
-- statement:
--   Given a uniform exact Stage I counting machine, there exist fixed deterministic enumeration and decoding machines and a common constant for all primes $p>3$ and elliptic Weierstrass curves over $\mathbf F_p$. The enumerator returns duplicate-free blocks: the entire group in the small regime, and the blocks of a seed from the winning full prefix otherwise. The decoder receives only the curve and the target, not the lists or seed; if the target is a sum of two elements from each of the enumerated blocks, it outputs such a decomposition. The enumerator meets the Stage I time and space bounds and the decoder meets the same time bound in polynomial space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 Proof of Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_ec_from_counts :
    CountOracle →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
       (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let b := bitLen p
          let m := blockCount b
          ∃ F : Fin m → List E.toAffine.Point,
            (∀ i : Fin m, (F i).Nodup) ∧
            ecBase E (fun i => (F i).toFinset) ∧
            RunsWithin M_enum out_enum (encodeCurveInput p E) (encodeECFactorBlocks F)
              (mainSpaceBound C b) (mainSpaceBound C b) ∧
            ∀ X : E.toAffine.Point,
              (∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X) →
              ∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X ∧
                RunsWithin M_dec out_dec
                  (Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)])
                  (encodeECDecomp A B)
                  (mainSpaceBound C b) (polyBound C b)) := by sorry
