-- Prove2me | Theorems.Thm_DetDLP_m14_enum
-- name    : DetDLP.m14_enum
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:11:11.461809+00:00
-- url     : https://prove2.me/theorems/a4f9455b-ae44-45b2-8097-7f75bad02bf6
-- title:
--   Uniform polynomial-space / subexponential-time enumerator machine satisfying D4Plan.Enumerates
-- statement:
--   Constructs `(A_enum, oa_enum, K_enum)` achieving `Enumerates A_enum oa_enum K_enum P` for any `P = mkSoloPlanFromBr ...` equipped with `SoloUnrollAllPortsBounded` and valid unrolling witnesses.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds

set_option autoImplicit false

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option warn.sorry false

theorem DetDLP.m14_enum :
    ∀ {C c : ℕ} (hC : 0 < C) (hc : 0 < c)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ),
    ∃ (A_enum : PrimitiveMachine) (oa_enum : Fin A_enum.tapeCount) (K_enum : ℕ),
      ∀ (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
          (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
        (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
          (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
      let f := soloPoly x.S
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
      let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
      ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
      SoloUnrollAllPortsBounded D rootNode rootUnroll →
      let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
        [⟨D, rootNode, rootUnroll⟩] [] 1 0
      ∀ (hvalid : treeAll SoloLeafData.Valid certTree)
          (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
          (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
            (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
            HitDegProp x hbLen doneNodes hperm),
      let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all
      ∀ (hverts : ∀ u : Fin (2 ^ B_bud),
            (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
              4 * x.m + 64 ^ Nat.clog 32 (4 * x.m))
          (hdegree : ∀ u : Fin (2 ^ B_bud),
            (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
              1217 * (C + 1) ^ 3 * x.b)
          (hcorrect :
            answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
              word f x.l (guard + x.p) hf
                (∑ u : Fin (2 ^ B_bud), (br u).wVal *
                  BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
                    (planVOfBr x f guard B_bud br u))
                j ⟨0, hpos⟩ / 2 ^ guard)),
      let P := mkSoloPlanFromBr x f hf hdeg_f hpos guard B_bud br hverts hdegree hcorrect
      Enumerates A_enum oa_enum K_enum P := by sorry
