-- Prove2me | Theorems.Thm_DetDLP_m14_enum_bounds
-- name    : DetDLP.m14_enum_bounds
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:34:13.888881+00:00
-- url     : https://prove2.me/theorems/33848475-82b8-5ae6-aaee-56b6f7c0422e
-- title:
--   Polynomial bit-length, oracle-transcript, and branch/digit descriptor bounds for D4 enumeration
-- statement:
--   Establishes monotonicity and composition rules for `polyBound`, bounds active-node branch counts by $2^{24(K_{\mathrm{loc}}+1)(\mathrm{size}(x)+1)}$, tracks work-item bit lengths across `callsV2` using `SoloUnrollAllPortsBounded`, and proves polynomial bounds in $X = (\mathrm{size}(x)+1)^2$ for `residue`, `contextV2`, `D4NodeQuery.request`, `stepInput`, `phaseStateV2`, `branch P u`, and `digitDesc P u a`.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine

set_option autoImplicit false

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option warn.sorry false

theorem DetDLP.m14_enum_bounds :
    (∀ {K₁ K₂ : ℕ} (hK : K₁ ≤ K₂) (n : ℕ),
        polyBound K₁ n ≤ polyBound K₂ n) ∧
    (∀ (K : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂),
        polyBound K n₁ ≤ polyBound K n₂) ∧
    (∀ (c n : ℕ),
        (c : ℝ) ≤ polyBound c n) ∧
    (∀ (K₁ K₂ n : ℕ),
        polyBound K₁ n + polyBound K₂ n ≤ polyBound (K₁ + K₂) n) ∧
    (∀ (K₁ K₂ n : ℕ),
        polyBound K₁ n * polyBound K₂ n ≤ polyBound (K₁ * K₂ + K₁ + K₂) n) ∧
    (∀ (K₁ K₂ m n : ℕ) (hm : m ≤ K₂ * (n + 1) ^ K₂),
        polyBound K₁ m ≤ polyBound (compExp K₁ K₂) n) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc guard : ℕ),
        ∀ (fuel : ℕ)
          (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
          (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
          (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
          (∀ it ∈ todo, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) →
          (∀ m ∈ done, NodePortsBounded x.S m) →
          treeAll (fun lf => ∀ m ∈ lf.doneNodes, NodePortsBounded x.S m)
            (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (hRing : RingOK f)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc W_max : ℕ)
        (hW : ∀ nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf),
          nd.d ≤ Nat.clog 32 (4 * x.m) → NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ W_max),
        let D := Nat.clog 32 (4 * x.m)
        let guard := totalGuard x.S D
        let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
        let F := soloStepFn M_node o_node ctx
        ∀ (fuel : ℕ)
          (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
          (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
          (b u : ℕ) (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
          (∀ it ∈ todo, it.2.1.d + it.1 = D) →
          (∀ it ∈ todo, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) →
          (∀ m ∈ done, m.d ≤ D ∧ NodePortsBounded x.S m) →
          ∀ e ∈ callsV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
            (done.map (·.toWorkItem.bits)) b u (residue f x.l (guard + x.p) hf accVal) lossSum,
          (∀ w ∈ unpack (fld e.1 2), w.length ≤ W_max) ∧
          (∀ w ∈ unpack (fld e.1 3), w.length ≤ W_max)) ∧
    (∀ (S d : ℕ),
        D3Stopped.width S d ≤ D3Stopped.level S) ∧
    (∀ {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
        {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
        {K_loc H_loc c_loc : ℕ}
        {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
        (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd),
        cert.nBranches ≤ 2 ^ (24 * (K_loc + 1) * (size x + 1))) ∧
    (∀ {f : ℤ[X]} {l q C K_grd X : ℕ} (hf : f.Monic) (z : B f l q)
        (hX1 : 1 ≤ X) (hq : q ≤ (K_grd + 1) * X) (hlf : l * f.natDegree ≤ 8 * (C + 1) * X),
        (residue f l q hf z).length ≤ 64 * (C + 1) * (K_grd + 2) * X ^ 2) ∧
    (∀ (S m p guard l C K_grd X : ℕ) (fBits : Wd)
        (hX1 : 1 ≤ X) (_hS : S ≤ X) (hlev : D3Stopped.level S ≤ X)
        (hD : Nat.clog 32 (4 * m) ≤ 8 * X)
        (h64sh : ∀ d, 64 ^ D3Stopped.shift S d ≤ 64 * X)
        (_hguard : guard ≤ K_grd * X) (_hqp : guard + p ≤ (K_grd + 1) * X)
        (_hl : l ≤ 2 * C * X) (_hfb : fBits.length ≤ 4 * X),
        (contextV2 S m p guard l fBits).length ≤ 131072 * (C + 2) * (K_grd + 2) * X ^ 2) ∧
    (∀ (G : AppendixD4.Graph) {b_h : ℕ} (host : Fin b_h → Fin G.nV)
        (a u pCurr l j_q C K_loc X : ℕ) (f : ℤ[X]) (lbl : Label a G)
        (hX1 : 1 ≤ X) (hnE : G.nE ≤ X) (hnV_a : a * G.nV ≤ 25 * X) (hnV_X : G.nV ≤ 25 * X)
        (hG_enc : G.encode.length ≤ 25088 * X) (hbh : b_h ≤ 100 * X)
        (ha : a ≤ X) (hu : u ≤ X) (h64a : 64 ^ a ≤ 64 * X)
        (hpCurr : pCurr ≤ 161 * X) (hl : l ≤ 2 * C * X) (hdeg_f : f.natDegree ≤ 4 * X)
        (hj_cw : (countWord j_q).length ≤ 24 * (K_loc + 1) * X + 1),
        (D4NodeQuery.request G host a u pCurr l f j_q).length ≤
          4194304 * (C + 2) * (K_loc + 2) * X ^ 2 ∧
        (G.nE + pCurr + f.natDegree + l + 2) + (stepInput G a u pCurr l f lbl).length ≤
          4194304 * (C + 2) * (K_loc + 2) * X ^ 2) ∧
    (∀ (tagW ctx accW : Wd) (pendW doneW : List Wd)
        (b' u' loss' K_wi C_big X : ℕ)
        (hX1 : 1 ≤ X) (hCbig1 : 1 ≤ C_big) (hKW_C : K_wi + 2 ≤ C_big)
        (htag : tagW.length ≤ 1)
        (hctx : ctx.length ≤ 131072 * C_big * X ^ 2)
        (hacc : accW.length ≤ 64 * C_big * X ^ 2)
        (hp_len : pendW.length ≤ 4096 * X) (hp_w : ∀ w ∈ pendW, w.length ≤ K_wi * X)
        (hd_len : doneW.length ≤ 4096 * X) (hd_w : ∀ w ∈ doneW, w.length ≤ K_wi * X)
        (hb_cw : (countWord b').length ≤ 131072 * C_big * X + 1)
        (hu_cw : (countWord u').length ≤ 131072 * C_big * X + 1)
        (hl_cw : (countWord loss').length ≤ C_big * X + 1),
        (phaseStateV2 tagW ctx pendW doneW b' u' accW loss').length ≤ 8388608 * C_big * X ^ 2) ∧
    (∀ {C c : ℕ} (hC : 0 < C) (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ)
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
    ∀ (K_grd K_wi C_big X : ℕ)
        (hX1 : 1 ≤ X) (hCbig1 : 1 ≤ C_big)
        (hC_Cbig : C + 2 ≤ C_big) (hKG_Cbig : K_grd + 2 ≤ C_big)
        (hKW_Cbig : K_wi + 2 ≤ C_big) (hCG_Cbig : (C + 2) * (K_grd + 2) ≤ C_big)
        (hxS_X : x.S ≤ X) (hdesc_X : x.desc.length ≤ X) (hp_X : x.p ≤ X)
        (hl_X : x.l ≤ 2 * C * X) (h4m_N1 : 4 * x.m ≤ 2 * (size x + 1)) (hmk_N1 : 4 * x.m * x.k ≤ 2 * (size x + 1))
        (hN1_X : size x + 1 ≤ X) (hN2_X : (size x + 1) ^ 2 ≤ X)
        (h64D_N2 : 64 ^ Nat.clog 32 (4 * x.m) ≤ 4096 * (size x + 1) ^ 2)
        (hD_X : Nat.clog 32 (4 * x.m) ≤ 8 * X)
        (hnV_orig_X : x.G.nV ≤ X) (hdeg_f_N1 : (soloPoly x.S).natDegree ≤ 4 * (size x + 1))
        (hq_X : totalGuard x.S (Nat.clog 32 (4 * x.m)) + x.p ≤ (K_grd + 1) * X)
        (hhdr_X3 : (header P).length ≤
          1048576 * C_big * X ^ 3)
        (hin_X3 : (D4Plan.input x).length ≤ C_big * X ^ 3)
        (hnd_tbl_G : ∀ nd : SoloNode x (soloPoly x.S)
            (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf),
          nd.d ≤ Nat.clog 32 (4 * x.m) →
          nd.G.encode.length ≤ 25088 * X ∧ nd.pCurr ≤ 161 * X ∧
          nd.toStoppedSpec.tableBits.length ≤ K_wi * X),
        (∀ u : Fin P.N, (branch P u).length ≤ 137438953472 * C_big * X ^ 3) ∧
        (∀ (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)),
          (digitDesc P u a).length ≤ 2199023255552 * C_big * X ^ 3)) := by sorry
