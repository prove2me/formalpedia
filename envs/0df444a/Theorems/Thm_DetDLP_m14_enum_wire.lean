-- Prove2me | Theorems.Thm_DetDLP_m14_enum_wire
-- name    : DetDLP.m14_enum_wire
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:01:11.543923+00:00
-- url     : https://prove2.me/theorems/eb391d4d-7c57-59c3-a1da-169f6834ad19
-- title:
--   One-call walker composition and raw I/O agreement with header and branches of soloPlan
-- statement:
--   Connects the raw polynomial-time pre/post codecs `preWalkGen` and `postWalkGen` around a single `PolyT` oracle call `soloOneCall`, proving exact equality between the raw padded rank walker pipeline output and the constructed `header P` / `branch P u` descriptions for any `P = mkSoloPlanFromBr ...`.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine

set_option autoImplicit false

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option warn.sorry false

theorem DetDLP.m14_enum_wire :
    (∀ (O : PrimitiveMachine) (o : Fin O.tapeCount)
        (pre post : Wd → Wd) (_hp : PolyT pre) (_hq : PolyT post),
        ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
          1 ≤ K ∧
          ∀ (q ans : Wd) (τ σ : ℝ) (M_len : ℕ),
            0 ≤ τ → 0 ≤ σ → ans ≠ [] →
            RunsWithin O o (pre q) ans τ σ →
            (callPair q []).length ≤ M_len →
            (callPair q (pre q)).length ≤ M_len →
            (callPair q ans).length ≤ M_len →
            ans.length ≤ M_len →
            (post (pack [q, ans])).length ≤ M_len →
            RunsWithin M out q (post (pack [q, ans]))
              (2 * (polyBound K M_len + (K : ℝ) * (τ + σ + 1)))
              (polyBound K M_len + (K : ℝ) * (σ + 1))) ∧
    (∀ {C c : ℕ} (x : Input C c) (n : ℕ)
        (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n) (degF l qPrec : ℕ),
        let w_re := getReattachWit x n leafFn
        lookupDescsRaw x.desc (D4Slice.field 8 (D4Plan.input x)) degF l qPrec =
          List.ofFn (fun v : Fin x.spec.lookupVerts.card =>
            lookupDesc x.desc (w_re.old v).val.val degF l qPrec)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
        (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
        (doneNodes : List (SoloNode x f PktOK))
        (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k)))
        (bi : Fin (4 * x.m * x.k)),
        findBoundaryLeaf (doneNodes.map (·.toWorkItem.bits)) bi.val =
          (hitLeafFn x hbLen doneNodes hperm (bi.cast hbLen.symm)).val) ∧
    (∀ {C c : ℕ} (x : Input C c) (_hL_level : 1 ≤ D3Stopped.level x.S)
        (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc j : ℕ) (hf : (soloPoly x.S).Monic),
        let f := soloPoly x.S
        let D := Nat.clog 32 (4 * x.m)
        let guard := totalGuard x.S D
        let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
        let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
        let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
        preWalkGen D4CoreCut.cutCoreRaw (A_fuel C K_loc) (8 * K_loc) (rankQuery x j) =
          startV2 ctx rootNode.toWorkItem B_bud (if j = 0 then 0 else j - 1)) ∧
    (∀ {C c : ℕ} (x : Input C c) (_hL_level : 1 ≤ D3Stopped.level x.S)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ)
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
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let F := soloStepFn M_node o_node ctx
    (∀ walkerOut : Wd,
      postWalkGen D4CoreCut.reattachRaw (A_fuel C K_loc) (8 * K_loc)
        (pack [rankQuery x 0, walkerOut]) = header P) ∧
    (∀ u : Fin P.N,
      let walkerOut := tag ((unrollRankTreeV2 ctx rootNode.toWorkItem F).read B_bud u.val)
      postWalkGen D4CoreCut.reattachRaw (A_fuel C K_loc) (8 * K_loc)
        (pack [rankQuery x (u.val + 1), walkerOut]) = branch P u)) := by sorry
