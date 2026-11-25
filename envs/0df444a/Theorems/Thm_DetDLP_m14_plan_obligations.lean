-- Prove2me | Theorems.Thm_DetDLP_m14_plan_obligations
-- name    : DetDLP.m14_plan_obligations
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:22:05.273807+00:00
-- url     : https://prove2.me/theorems/f3649df8-ce5d-5a9a-a30e-78fa5ea6e5b0
-- title:
--   Reattachment port alignment, stopped branch constructors, and algebraic correctness for D4 solo plans
-- statement:
--   Bundles six structural and algebraic obligations required to assemble a `Plan x` via `mkSoloPlanFromBr` and `mkPlanBranchAux`:
--
--   1. Reattachment witness consistency (`w.old` matches `lookupVerts`, `w.lp` preserves port indices).
--   2. Empty stopped descriptor identity (`emptyStoppedSpec`).
--   3. Root boundary-pin permutation identity.
--   4. Hit-branch vertex degree preservation (`HitDegProp`).
--   5. Exact `none` and `some` branch reduction equations for `mkPlanBranchAux`.
--   6. Global vertex count, max-degree ($\mathrm{maxDeg} \cdot m \le 1217(C+1)^3 b$), and exact algebraic reconstruction of `answer x` from `(br u).wVal * BTNContract ...`.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_adaptive_padded_rank_sum
set_option autoImplicit false
open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option warn.sorry false

theorem DetDLP.m14_plan_obligations :
    (∀ {C c : ℕ} (x : Input C c) (n : ℕ) (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n),
      let w := getReattachWit x n leafFn
      (∀ v, (w.old v).val = (D4CoreCut.lookupVerts x.G x.spec.lookupVerts)[v.val]'(by
        rw [D4CoreCut.lookup_length]; exact v.isLt)) ∧
      (∀ v i, (w.lp v i).val = i.val)) ∧
    (∀ {C c : ℕ} (x : Input C c) (f : ℤ[X]) (deg : ℕ),
      (emptyStoppedSpec x f deg).tableBits = pack [] ∧
      stoppedDesc x.desc x.S x.l x.p 0 f emptyGraphConst (emptyStoppedSpec x f deg).tableBits =
        emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l) ∧
    (∀ {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l),
      pinFirsts ([rootSoloNode x f PktOK] : List (SoloNode x f PktOK)) =
        List.finRange (4 * x.m * x.k)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
      (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
      (doneNodes : List (SoloNode x f PktOK))
      (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
      HitDegProp x hbLen doneNodes hperm) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
      (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard B_bud : ℕ)
      (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
      (hvalid : treeAll SoloLeafData.Valid certTree)
      (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
      (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
        HitDegProp x hbLen doneNodes hperm)
      (u : Fin (2 ^ B_bud)),
      (certTree.read B_bud u.val = none →
        mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u =
          let L := x.spec.lookupVerts
          let lfFn := missLeafFn x hbLen
          let H := D4CoreCut.reattach x.G L (4 * x.m) lfFn
          ⟨4 * x.m, lfFn, 0,
            fun _ => emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l,
            fun j β => (emptyStoppedSpec x f (H.deg (Fin.natAdd L.card j))).value hf x.A (guard + x.p) β⟩) ∧
      (∀ lf (hsome : certTree.read B_bud u.val = some lf),
        mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u =
          let hlf : lf.Valid := treeAll_read hvalid B_bud u.val hsome
          let lfFn := hitLeafFn x hbLen lf.doneNodes hlf.2.2.2
          ⟨lf.doneNodes.length, lfFn, lf.weight,
            fun j =>
              let nd := lf.doneNodes.get j
              stoppedDesc x.desc x.S x.l nd.pCurr nd.d f nd.G nd.toStoppedSpec.tableBits,
            fun j β =>
              let nd := lf.doneNodes.get j
              let hdeg := hdeg_all lf.doneNodes hlf.2.2.2 j
              nd.toStoppedSpec.value hf x.A (guard + x.p) (fun kp => β (kp.cast hdeg.symm))⟩)) ∧
    (∀ {C c : ℕ} (hC : 0 < C) (x : Input C c)
      (hL_level : 1 ≤ D3Stopped.level x.S)
      (hf : (soloPoly x.S).Monic)
      (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc : ℕ)
      (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
      (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
      (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
        (Nat.clog 32 (4 * x.m))
        (rootSoloNode x (soloPoly x.S)
          (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf)))
      (hvalid : treeAll SoloLeafData.Valid
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
          (totalGuard x.S (Nat.clog 32 (4 * x.m))) (64 ^ Nat.clog 32 (4 * x.m))
          [⟨Nat.clog 32 (4 * x.m),
            rootSoloNode x (soloPoly x.S)
              (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf),
            rootUnroll⟩] [] 1 0))
      (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
      (hdeg_all : ∀ (doneNodes : List (SoloNode x (soloPoly x.S)
          (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf)))
        (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
        HitDegProp x hbLen doneNodes hperm)
      (hpos : 0 < (soloPoly x.S).natDegree),
      let f := soloPoly x.S
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
      let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
        [⟨D, rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf), rootUnroll⟩] [] 1 0
      let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all
      (∀ u : Fin (2 ^ B_bud),
        (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
          4 * x.m + 64 ^ Nat.clog 32 (4 * x.m)) ∧
      (∀ u : Fin (2 ^ B_bud),
        (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
          1217 * (C + 1) ^ 3 * x.b) ∧
      (answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
        word f x.l (guard + x.p) hf
          (∑ u : Fin (2 ^ B_bud), (br u).wVal *
            BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
              (planVOfBr x f guard B_bud br u))
          j ⟨0, hpos⟩ / 2 ^ guard))) := by sorry
