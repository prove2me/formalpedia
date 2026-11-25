-- Prove2me | Theorems.Thm_DetDLP_m14_sources
-- name    : DetDLP.m14_sources
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:47:57.41781+00:00
-- url     : https://prove2.me/theorems/0ed513bc-d925-4b64-ba08-5cf23ef6151e
-- title:
--   Conditional source evaluator machine for D4 solo plans under AppendixD4.Closed
-- statement:
--   Shows that given any local rank machine `(M_node, E_pkt)` and entry machine `(E, o)`, there exists an a priori threshold $L_{0,\mathrm{src}}$ (chosen independently of assuming `AppendixD4.Closed`) such that whenever `AppendixD4.Closed` holds, there is a source evaluator machine `(B_src, ob_src, k_src)` realizing `Sources B_src ob_src k_src P` for every `P = mkSoloPlanFromBr ...` above the level thresholds.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_active_node_preconditions

set_option autoImplicit false

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option warn.sorry false

theorem DetDLP.m14_sources :
    ∀ {C c : ℕ} (hC : 0 < C) (hc : 0 < c)
        (E : PrimitiveMachine) (o : Fin E.tapeCount)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ),
    ∃ L₀_src_opt : ℕ, AppendixD4.Closed →
      ∃ (B_src : PrimitiveMachine) (ob_src : Fin B_src.tapeCount) (k_src : ℕ),
        ∀ (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
            (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
        (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
            (hL_act : max 6 (DetDLP.d4_active_node_preconditions C hC).choose ≤ D3Stopped.level x.S)
            (hL_src : max (C + 6) L₀_src_opt ≤ D3Stopped.level x.S) (he : entry x E o)
            (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
        let f := soloPoly x.S
        let D := Nat.clog 32 (4 * x.m)
        let guard := totalGuard x.S D
        let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
        let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
        ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
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
        Sources B_src ob_src k_src P := by sorry
