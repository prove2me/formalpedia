-- Prove2me | Theorems.Thm_DetDLP_m89_s1_ec_plan_decode
-- name    : DetDLP.m89_s1_ec_plan_decode
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:35:26.237987+00:00
-- url     : https://prove2.me/theorems/399fe5d7-3a8f-4950-963a-da1bcfa75359
-- title:
--   Find a target witness from a supplied elliptic curve plan
-- statement:
--   From a valid plan and a representable target, find a full tuple by following nonempty target-constrained pair prefixes. In the full-group branch a fixed decomposition suffices. Only polynomial visited space is available, and the decoder is not given block lists.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_DetDLP_M89_S1_Plans
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_ec_plan_decode : CountOracle → ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic], 
      let b := bitLen p; let m := blockCount b
      ∀ L : Option (ℕ × ECSeed p m), m89_ec_plan_ok E L → ∀ X : E.toAffine.Point,
        (∃ A B : Fin m → E.toAffine.Point, (∀ i, A i ∈ m89_ec_plan_block E L i ∧ B i ∈ m89_ec_plan_block E L i) ∧ (∑ i, (A i + B i)) = X) →
        ∃ A B : Fin m → E.toAffine.Point, (∀ i, A i ∈ m89_ec_plan_block E L i ∧ B i ∈ m89_ec_plan_block E L i) ∧ (∑ i, (A i + B i)) = X ∧
          RunsWithin M o (Encoding.encodeList id [(Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)]),m89_ec_plan_word L]) (encodeECDecomp A B) (mainSpaceBound K b) (polyBound K b) := by sorry
