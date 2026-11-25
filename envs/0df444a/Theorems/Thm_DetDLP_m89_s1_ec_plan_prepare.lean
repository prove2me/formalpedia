-- Prove2me | Theorems.Thm_DetDLP_m89_s1_ec_plan_prepare
-- name    : DetDLP.m89_s1_ec_plan_prepare
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:35:04.856982+00:00
-- url     : https://prove2.me/theorems/fe64e89b-25b1-47cf-ad7c-aaef44fd4e15
-- title:
--   Select and serialize the elliptic curve seed
-- statement:
--   Given exact prefix-moment counts, compute the full-group marker or the threshold and winning seed. Two fixed preprocessing machines, on the enumeration input and the target input respectively, append the same plan to the original word. Both use polynomial visited space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_DetDLP_M89_S1_Plans
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_ec_plan_prepare : CountOracle → ∃ (U : PrimitiveMachine) (u : Fin U.tapeCount) (V : PrimitiveMachine) (v : Fin V.tapeCount) (J : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic], 
      let b := bitLen p; let m := blockCount b
      ∃ L : Option (ℕ × ECSeed p m), m89_ec_plan_ok E L ∧
        RunsWithin U u (encodeCurveInput p E) (Encoding.encodeList id [(encodeCurveInput p E),m89_ec_plan_word L]) (mainSpaceBound J b) (polyBound J b) ∧
        ∀ X : E.toAffine.Point, RunsWithin V v (Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)]) (Encoding.encodeList id [(Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)]),m89_ec_plan_word L]) (mainSpaceBound J b) (polyBound J b) := by sorry
