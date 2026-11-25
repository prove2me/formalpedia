-- Prove2me | Theorems.Thm_DetDLP_m14_total
-- name    : DetDLP.m14_total
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:17:40.442617+00:00
-- url     : https://prove2.me/theorems/e077441a-9516-4d97-8af7-01b465208b64
-- title:
--   Root tree contraction identity for fuel-bounded D4 solo unrolling
-- statement:
--   Establishes that for any root solo node `rootNode` at depth $0$ with $\deg(f) > 0$, guard $g = \mathrm{totalGuard}(x.S, D)$, precision $q = g + x.p$, and boundary assignment $\eta : \mathrm{Fin}(4mk) \to \mathrm{Bool}$, the weighted leaf sum of `unrollCertFuel` equals $2^g$ times the root pinned tensor contraction:
--
--   $$\mathrm{Tree.total}(\lambda \ell.\; \ell.\mathrm{weight} \cdot \ell.\mathrm{doneProd}(\eta))(\mathrm{unrollCertFuel}\;\cdots) = (2 : B_{f, x.l, q})^g \cdot \mathrm{SoloNode.pinnedVal}_{h_f, q}(\eta, \mathrm{rootNode}).$$
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
set_option autoImplicit false
open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m14_total :
    ∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic),
    0 < f.natDegree →
    ∀ (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc : ℕ)
      (rootNode : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
      rootNode.d = 0 →
      ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
          (Nat.clog 32 (4 * x.m)) rootNode)
        (η : Fin (4 * x.m * x.k) → Bool),
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      let q := guard + x.p
      D4RankCode.Tree.total (fun lf => lf.weight * lf.doneProd η)
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
          [⟨D, rootNode, rootUnroll⟩] [] 1 0) =
      (2 : B f x.l q) ^ guard * SoloNode.pinnedVal hf q η rootNode := by sorry
