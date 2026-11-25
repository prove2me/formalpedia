-- Prove2me | Theorems.Thm_DetDLP_d4_stopped_local_entry_machine
-- name    : DetDLP.d4_stopped_local_entry_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:48:57.92434+00:00
-- url     : https://prove2.me/theorems/d7f6e4df-6c16-4f65-bed6-fc813ef22615
-- title:
--   Uniform evaluation of pinned original and packet entries
-- statement:
--   Fix an original-entry machine and a packet machine. For every stopped graph with a valid routing table, one machine evaluates all pinned vertex entries. Assume the local input, the selected oracle queries and replies, and oracle space are polynomially bounded in the scale plus the pinned payload length. If the two oracle times are positive, the evaluator takes polynomial overhead times their sum and only polynomial space. The machine accepts the framed vertex query itself; no table of evaluated tensor entries is supplied.
-- source:
--   Worker M14-StoppedSrc item 3; Appendix D.4 port-query and packet interfaces.

import Definitions.Def_DetDLP_D4StoppedNode
set_option autoImplicit false
open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.d4_stopped_local_entry_machine (E F : PrimitiveMachine) (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) (c : ℕ) :
    ∃ (L : PrimitiveMachine) (oL : Fin L.tapeCount) (k : ℕ),
    ∀ (S P l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (A : Tensor origG (Fin l → ℕ))
      (α : Fin deg → Bool) (To Tp : ℕ),
      let payload := s.payload origDesc α
      let n := S+payload.length
      let desc := D3Stopped.descOf d f payload
      1 ≤ To → 1 ≤ Tp → (∀ v t j, A v t j < 2^P) →
      (∀ (w : Fin G.nV) (β : Fin (G.deg w) → Bool), (encodePortQuery desc w.val (List.ofFn β)).length ≤ c*(n+1)^c) →
      (∀ v t, let inp := encodePortQuery origDesc v.val (List.ofFn t)
              let ans := encodeNatListBin (List.ofFn (A v t))
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin E oE inp ans To (polyBound c n)) →
      (∀ w pkt (h : s.vTable w = .pkt pkt) β, let p := s.packet w pkt h
              let inp := Encoding.encodeList id [pkt,List.ofFn β]
              let ans := residue f l p.creation hf (p.entry β)
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin F oF inp ans Tp (polyBound c n)) →
      ∀ w β, RunsWithin L oL (encodePortQuery desc w.val (List.ofFn β)) (residue f l P hf (s.entry hf A α w β))
        (polyBound k n * (To + (Tp : ℝ))) (polyBound k n) := by sorry
