-- Prove2me | Theorems.Thm_DetDLP_m14_bounds
-- name    : DetDLP.m14_bounds
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:01:26.536175+00:00
-- url     : https://prove2.me/theorems/86906998-003f-51ca-bb12-889b68f1adb9
-- title:
--   Encoding length, parameter rate, schedule shift, and port-bound invariants for D4 solo enumeration
-- statement:
--   Establishes 17 quantitative encoding and port-boundedness invariants for Milestone 14, including `countWord`/`encodeNatListBin`/`pack`/`BipartiteMultigraph.encode`/`residue` bit-length bounds, input-parameter bounds ($4mk \le 2S$, $G.\mathrm{nE} \le 3S$), polynomial input length (`size x`), the source-to-plan rate inequality $K_B S / \sqrt{\mathrm{level}(S)} \le 9(C+1)^3 K_B (b/m)$ for $C + 6 \le \mathrm{level}(S)$, leaf depth and `D3Stopped.cap` degree bounds, work-item bit-length bounds `soloNode_table_and_work_len`, and preservation of `SoloUnrollAllPortsBounded` across `buildSoloUnroll`.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Definitions.Def_DetDLP_W5_M6DriverFrames
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
import Theorems.Thm_DetDLP_d4_active_node_preconditions

set_option autoImplicit false
open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs DetDLP.w5_SplitArithmetic
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option warn.sorry false

theorem DetDLP.m14_bounds :
    (∀ n : ℕ, (countWord n).length ≤ n + 1) ∧
    (∀ {a m : ℕ}, a ≤ 2 ^ m → (countWord a).length ≤ m + 1) ∧
    (∀ (ns : List ℕ) (b : ℕ), (∀ n ∈ ns, (countWord n).length ≤ b) →
      (encodeNatListBin ns).length ≤ (2 * b + 2) * ns.length + 1) ∧
    (∀ (ws : List Wd) (b : ℕ), (∀ w ∈ ws, w.length ≤ b) →
      (pack ws).length ≤ (2 * b + 2) * ws.length + 1) ∧
    (∀ G : BipartiteMultigraph, G.encode.length ≤ 32 * (G.nV + G.nE + 2) ^ 2) ∧
    (∀ (f : ℤ[X]) (l q : ℕ) (hf : f.Monic) (z : B f l q),
      (residue f l q hf z).length ≤ (2 * (q + 1) + 2) * (l * f.natDegree) + 1) ∧
    (∀ K u : ℕ, polyBound K u = ((K * (u + 1) ^ K : ℕ) : ℝ)) ∧
    (∀ S j : ℕ, D3Stopped.shift S j ≤ D3Stopped.level S / 32768) ∧
    (∀ {C c : ℕ} (x : Input C c),
      4 * x.m * x.k ≤ 2 * x.S ∧ x.G.nE ≤ 3 * x.S ∧ x.m ≤ 2 * x.S ∧ x.k ≤ 2 * x.S ∧
      x.b ≤ 2 * C * x.S ∧ x.l ≤ 2 * C * x.S ∧ x.p ≤ x.S ∧ x.S ≤ size x ∧ x.desc.length ≤ size x) ∧
    (∀ {C c : ℕ}, 0 < c → ∃ K_in : ℕ, 1 ≤ K_in ∧ ∀ x : Input C c,
      (D4Plan.input x).length ≤ K_in * (size x + 1) ^ K_in) ∧
    (∀ {C c : ℕ} (x : Input C c) (K_B : ℕ), C + 6 ≤ D3Stopped.level x.S →
      (K_B : ℝ) * (x.S : ℝ) / Real.sqrt (D3Stopped.level x.S : ℝ) ≤
        ((9 * (C + 1) ^ 3 * K_B : ℕ) : ℝ) * ((x.b : ℝ) / (x.m : ℝ))) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
      (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc guard : ℕ),
      let D := Nat.clog 32 (4 * x.m)
      ∀ (fuel : ℕ)
        (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
        (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
        (∀ it ∈ todo, it.2.1.d + it.1 = D) →
        (∀ m ∈ done, m.d ≤ D) →
        treeAll (fun lf => ∀ m ∈ lf.doneNodes, m.d ≤ D)
          (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum)) ∧
    (∀ {C c : ℕ} (hC : 0 < C) (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
      (nd : SoloNode x f PktOK),
      max 6 (DetDLP.d4_active_node_preconditions C hC).choose ≤ D3Stopped.level x.S →
      nd.G.maxDeg ≤ D3Stopped.cap x.S) ∧
    (∀ {E_pkt : PrimitiveMachine} {oe : Fin E_pkt.tapeCount} {K_loc C c : ℕ}
      {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
      {dCreate pCreate origDeg : ℕ} {rawDesc : Bits} {entry₀ : (Fin origDeg → Bool) → B f x.l pCreate},
      pktOKOf E_pkt oe K_loc x f hf dCreate pCreate origDeg rawDesc entry₀ →
      (origDeg : ℝ) ≤ polyBound K_loc (pCreate + 4 * D3Stopped.level x.S + x.l + 2)) ∧
    (∀ {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l),
      NodePortsBounded x.S (rootSoloNode x f PktOK)) ∧
    (∀ {C c : ℕ} (K_loc : ℕ), ∃ K_wi : ℕ, 1 ≤ K_wi ∧
      ∀ (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount)
        (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
        nd.d ≤ Nat.clog 32 (4 * x.m) →
        nd.toStoppedSpec.tableBits.length ≤ K_wi * (size x + 1) ^ K_wi ∧
        (NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ K_wi * (size x + 1) ^ K_wi)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic) (hRing : RingOK f)
      (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
      (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc : ℕ)
      (hLocal : ∀ (G : Graph) (a u p l b τ : ℕ) (host : Fin b → Fin G.nV) (f' : ℤ[X]) (hf' : f'.Monic),
        1 ≤ u → (hu : u ≤ a) → u ≤ G.nE → 1 ≤ l → 1 ≤ p → RingOK f' → points G.nE a ≤ 2 ^ f'.natDegree →
        2 ^ a * 64 ^ (2 * a) ≤ G.nE → (a + 2) * 64 ^ (4 * a) * max 1 G.maxDeg ≤ G.nE → 1 ≤ τ →
        (∀ z, (Finset.univ.filter fun y => host z = host y).card ≤ τ) →
        ∃ (lbl : Label a G) (s : Step lbl hu f' l p) (order : Fin (Fintype.card (Branch s)) ≃ Branch s),
          let n := G.nE + p + f'.natDegree + l + 2
          let bound (j : ℕ) := polyBound H_loc (D4NodeQuery.request G host a u p l f' j).length +
            polyBound K_loc (n + (stepInput G a u p l f' lbl).length) + c_loc
          D2.Balanced host τ lbl ∧ Padded lbl ∧ s.sound hf' ∧
          (∀ t, ((s.modes t).count : ℝ) ≤ Real.exp ((K_loc : ℝ) * Real.sqrt
            ((G.nE : ℝ) * (p + increase G.nE a u (AppendixD4.level t.val)) / tileScale a (AppendixD4.level t.val)))) ∧
          RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' 0)
            (countWord (Fintype.card (Branch s))) (bound 0) (bound 0) ∧
          (∀ j, RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' (j.val + 1))
            (s.bits hf' (order j)) (bound (j.val + 1)) (bound (j.val + 1))) ∧
          ∀ t k β g r α, let z := s.child t k β g
            RunsWithin E_pkt o_pkt (Encoding.encodeList id [z.descriptor r, List.ofFn α])
              (residue f' l _ hf' (z.entry r α))
              (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
      (L₀_act : ℕ)
      (hact_all : ∀ (d M Δ p : ℕ),
        L₀_act ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8 ^ d →
        let a := D3Stopped.shift x.S d; let u := D3Stopped.width x.S d
        let last := if d = 0 then 0 else D3Stopped.shift x.S (d - 1)
        Δ ≤ max (C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4))) (2 * 2 ^ last) →
        p ≤ x.p + 80 * x.S * 2 ^ last →
        1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧ points M a ≤ 2 ^ (4 * D3Stopped.level x.S) ∧
        2 ^ a * 64 ^ (2 * a) ≤ M ∧ (a + 2) * 64 ^ (4 * a) * max 1 Δ ≤ M ∧
        max Δ (2 * 2 ^ a) ≤ D3Stopped.cap x.S ∧
        (∀ i < u, p + increase M a u i ≤ 64 * M * tileScale a i / u) ∧
        ∀ i, p + increase M a u i ≤ x.p + 80 * x.S * 2 ^ a)
      (hL : L₀_act ≤ D3Stopped.level x.S)
      (k : ℕ) (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
      (hk : nd.d + k = Nat.clog 32 (4 * x.m)),
      NodePortsBounded x.S nd →
      SoloUnrollAllPortsBounded k nd
        (buildSoloUnroll x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc hLocal L₀_act hact_all hL k nd hk)) := by sorry
