-- Prove2me | Theorems.Thm_DetDLP_m89_s1_ec_plan_enumerate
-- name    : DetDLP.m89_s1_ec_plan_enumerate
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:35:01.365294+00:00
-- url     : https://prove2.me/theorems/f55f9498-59cb-4bb1-9654-ecf1687bc7a0
-- title:
--   Enumerate blocks from a supplied elliptic curve plan
-- statement:
--   Given a valid plan on the input tape and an exact count oracle, output each block without duplicates, with the prescribed set of elements. The large branch uses the element-prefix queries; the small branch enumerates the full group. No seed selection or target decomposition is required.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_DetDLP_M89_S1_Plans
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_ec_plan_enumerate : CountOracle → ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic], 
      let b := bitLen p; let m := blockCount b
      ∀ L : Option (ℕ × ECSeed p m), m89_ec_plan_ok E L → ∃ F : Fin m → List E.toAffine.Point,
        (∀ i, (F i).Nodup ∧ (F i).toFinset = m89_ec_plan_block E L i) ∧
        RunsWithin M o (Encoding.encodeList id [(encodeCurveInput p E),m89_ec_plan_word L]) (encodeECFactorBlocks F) (mainSpaceBound K b) (mainSpaceBound K b) := by sorry
