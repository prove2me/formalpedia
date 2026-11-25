-- Prove2me | Theorems.Thm_DetDLP_m14_sync
-- name    : DetDLP.m14_sync
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:46:13.917018+00:00
-- url     : https://prove2.me/theorems/c27ef468-6b34-5d1a-934d-e3f620c239fc
-- title:
--   Synchronization, validity, budget work, and call-coverage invariants for fuel-bounded D4 solo unrolling
-- statement:
--   Establishes four operational invariants linking certified partial unrolling `unrollCertFuel` to the padded rank walker `unrollAuxV2` and its transcript `callsV2` over an instance $x$ of `Input C c`, monic $f \in \mathbb{Z}[X]$, and $D = \lceil \log_{32}(4m) \rceil$:
--
--   $$(1)\; \mathrm{treeMap}(\mathrm{SoloLeafData.toBits}\;\mathrm{ctx})(\mathrm{unrollCertFuel}\;\cdots) = \mathrm{unrollAuxV2}\;\mathrm{ctx}\;F\;\mathrm{fuel}\;\cdots$$
--
--   $$(2)\; \mathrm{treeAll}(\mathrm{SoloLeafData.Valid})(\mathrm{unrollCertFuel}\;\cdots), \qquad (3)\; \mathrm{D4UnrollBudget.Work}\;x.S\;D\;(8K_{\mathrm{loc}})\;\cdots$$
--
--   $$(4)\; \forall e \in \mathrm{callsV2}\;\cdots,\; \mathrm{CallCovered}\;x\;h_f\;M_{\mathrm{node}}\;E_{\mathrm{pkt}}\;\cdots\;e.$$
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine
set_option autoImplicit false
open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m14_sync :
    ∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ),
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let F := soloStepFn M_node o_node ctx
    (RingOK f →
      ∀ (fuel : ℕ)
        (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
        (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
        remSlots todo ≤ fuel →
        treeMap (SoloLeafData.toBits ctx)
          (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) =
        unrollAuxV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
          (done.map (·.toWorkItem.bits)) (residue f x.l (guard + x.p) hf accVal) lossSum) ∧
    (∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      lossSum + localAllowance x.S D * remSlots todo ≤ guard →
      done.length + remLeaves todo ≤ 64 ^ D →
      (∀ m ∈ done, D ≤ m.d ∨ m.G.nE ≤ D3Stopped.threshold x.S) →
      List.Perm (pinFirsts (done ++ todoNodes todo)) (List.finRange (4 * x.m * x.k)) →
      treeAll SoloLeafData.Valid
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum)) ∧
    (∀ (g_arg fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (g_arg + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      D4UnrollBudget.Work x.S D (8 * K_loc)
        ((todoNodes todo).map fun nd => (nd.d, nd.G.nE))
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc g_arg fuel todo done accVal lossSum)) ∧
    (RingOK f →
      ∀ (bBudget fuel : ℕ)
        (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
        (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (b u : ℕ) (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
        (∀ it ∈ todo, it.2.1.d + it.1 = D) →
        (∀ m ∈ done, m.d ≤ D) →
        lossSum + localAllowance x.S D * remSlots todo ≤ guard →
        done.length + remLeaves todo ≤ 64 ^ D →
        b ≤ bBudget →
        u < 2 ^ bBudget →
        ∀ e ∈ callsV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
          (done.map (·.toWorkItem.bits)) b u (residue f x.l (guard + x.p) hf accVal) lossSum,
        CallCovered x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard bBudget e) := by sorry
