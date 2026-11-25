-- Prove2me | Theorems.Thm_DetDLP_m14_pkt
-- name    : DetDLP.m14_pkt
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T07:11:43.581187+00:00
-- url     : https://prove2.me/theorems/11cfb4e0-27e9-4a15-a760-c2489678bdee
-- title:
--   Lookup-query length lower bound, packet evaluator adapter machine, and source/stopped polynomial length reductions
-- statement:
--   Establishes four components supporting source evaluation:
--
--   1. Query-length lower bound $\kappa \le |\mathrm{encodePortQuery}(\mathrm{lookupDesc}\;\cdots)|$ when $2^{\kappa / 4} \le q$.
--   2. Existence of a polynomial-time packet adapter machine $(F_{\mathrm{pkt}}, o_{F,\mathrm{pkt}}, K_{\mathrm{pkt}})$ evaluating every packet vertex inside a stopped `SoloNode` within $\exp(K_{\mathrm{pkt}} \cdot 2^{\mathrm{shift}(x.S, \mathrm{nd}.d - 1)} \log n_{\mathrm{pkt}})$ time and polynomial space.
--   3. Uniform polynomial degree collapsing helpers `source_lengths_from_bounds` and `stopped_lengths_from_bounds`.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Definitions.Def_DetDLP_W1_Pipeline

set_option autoImplicit false
open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option warn.sorry false

theorem DetDLP.m14_pkt :
    (∀ (origDesc : Bits) (j κ l q v : ℕ) (α : List Bool),
      2 ^ (κ / 4) ≤ q → κ = 4 * (κ / 4) →
      κ ≤ (encodePortQuery (lookupDesc origDesc j κ l q) v α).length) ∧
    (∀ (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc : ℕ),
      ∃ (F_pkt : PrimitiveMachine) (oF_pkt : Fin F_pkt.tapeCount) (K_pkt : ℕ),
        1 ≤ K_pkt ∧
        ∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
          (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
          (w : Fin nd.G.nV) (pkt : Bits) (h : nd.toStoppedSpec.vTable w = .pkt pkt)
          (β : Fin (nd.G.deg w) → Bool),
          let p := nd.toStoppedSpec.packet w pkt h
          let n_pkt := nd.G.nE + p.creation + 4 * D3Stopped.level x.S + x.l + 2
          let inp := Encoding.encodeList id [pkt, List.ofFn β]
          let ans := residue f x.l p.creation hf (p.entry β)
          inp.length ≤ K_pkt * (n_pkt + 1) ^ K_pkt ∧
          RunsWithin F_pkt oF_pkt inp ans
            (Real.exp ((K_pkt : ℝ) * (2 ^ D3Stopped.shift x.S (nd.d - 1) : ℕ) * Real.log n_pkt))
            (polyBound K_pkt n_pkt)) ∧
    ((C c K_grd K_wi K_pkt c_pkt : ℕ) →
      ∃ c_src : ℕ, c ≤ c_src ∧ 1 ≤ c_src ∧
        ∀ (N₁ : ℕ), 1 ≤ N₁ →
          ∀ (descLen jVal κ l q vVal αLen yLen xLen uLen : ℕ),
            descLen ≤ N₁ → jVal ≤ N₁ ^ c → κ ≤ 4 * N₁ → l ≤ 2 * C * N₁ →
            q ≤ (K_grd + 1) * N₁ ^ (K_grd + 1) → vVal ≤ 65544 * N₁ ^ 2 → αLen ≤ 3 * N₁ →
            uLen ≤ 64 * (descLen + jVal + κ + l + q + vVal + αLen + 4) →
            xLen ≤ 16 * (descLen + jVal + αLen + 4) →
            yLen ≤ (2 * N₁ + 4) * l + 1 →
            uLen ≤ c_src * N₁ ^ c_src ∧
            xLen ≤ c_src * N₁ ^ c_src ∧
            yLen ≤ c_src * N₁ ^ c_src) ∧
    ((C c K_grd K_wi K_pkt c_pkt : ℕ) →
      ∃ c_s2 : ℕ, c ≤ c_s2 ∧ 1 ≤ c_s2 ∧
        ∀ (N₁ n₁ m₁ : ℕ), 2 ≤ N₁ → N₁ ≤ n₁ → n₁ ≤ m₁ →
          (25 * m₁ ^ (c + 2) ≤ m₁ ^ c_s2) ∧
          (K_pkt * ((2 * N₁) ^ c_pkt + 1) ^ K_pkt ≤ c_s2 * n₁ ^ c_s2) ∧
          ∀ (uLen xStopLen yStopLen qStopLen : ℕ),
            uLen ≤ 1048576 * (C + 2) * (K_wi + 2) * N₁ ^ (max (2 * c + 6) (K_wi + 4)) →
            xStopLen ≤ 1048576 * (C + 2) * (K_wi + 2) * N₁ ^ (max (2 * c + 6) (K_wi + 4)) →
            yStopLen ≤ 1048576 * (C + 2) * N₁ ^ 6 →
            qStopLen ≤ 1048576 * (C + 2) * (K_wi + 2) * n₁ ^ (max (c + 4) (K_wi + 4)) →
            uLen ≤ c_s2 * N₁ ^ c_s2 ∧
            xStopLen ≤ c_s2 * N₁ ^ c_s2 ∧
            yStopLen ≤ c_s2 * N₁ ^ c_s2 ∧
            qStopLen ≤ c_s2 * n₁ ^ c_s2) := by sorry
