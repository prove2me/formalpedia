-- Prove2me | Theorems.Thm_DetDLP_d4_stopped_continuation_bridge
-- name    : DetDLP.d4_stopped_continuation_bridge
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:16:07.037748+00:00
-- url     : https://prove2.me/theorems/1747feb0-7f47-437c-ba5f-b04070b3dc98
-- title:
--   Pinned contraction with concrete local-entry machines
-- statement:
--   Given the closed contraction hypothesis, a stopped graph with the scheduled edge, degree and precision bounds can be evaluated on a pinned assignment. One continuation machine suffices for every such graph; its local running time is polynomial overhead times the sum of original and packet budgets.

import Definitions.Def_DetDLP_D4StoppedNode
set_option autoImplicit false
open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.d4_stopped_continuation_bridge (hClosed : AppendixD4.Closed) (C c : ℕ) (hC : 0 < C)
    (E F : PrimitiveMachine) (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k L₀ r : ℕ),
    ∀ (S P q l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (A : Tensor origG (Fin l → ℕ))
      (α : Fin deg → Bool) (To Tp : ℕ),
      let payload := s.payload origDesc α
      let n := S+payload.length
      let desc := D3Stopped.descOf d f payload
      let m := S+desc.length
      let T := (r+1)*(n+1)^r*(To+Tp)
      D3Stopped.level S ≥ L₀ → G.nE ≤ C*S/8^d → G.maxDeg ≤ D3Stopped.cap S →
      G.nV ≤ (m+1)^c → 1 ≤ P → P ≤ S+80*C*S*(if d=0 then 1 else 2^D3Stopped.shift S (d-1)) →
      1 ≤ l → l ≤ C*S → RingOK f → f.natDegree = 4*D3Stopped.level S → P ≤ q →
      1 ≤ To → 1 ≤ Tp → (∀ v t j, A v t j < 2^P) →
      (∀ (w : Fin G.nV) (β : Fin (G.deg w) → Bool), (encodePortQuery desc w.val (List.ofFn β)).length ≤ c*(n+1)^c) →
      (∀ v t, let inp := encodePortQuery origDesc v.val (List.ofFn t)
              let ans := encodeNatListBin (List.ofFn (A v t))
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin E oE inp ans To (polyBound c n)) →
      (∀ w pkt (h : s.vTable w = .pkt pkt) β, let p := s.packet w pkt h
              let inp := Encoding.encodeList id [pkt,List.ofFn β]
              let ans := residue f l p.creation hf (p.entry β)
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin F oF inp ans Tp (polyBound c n)) →
      RunsWithin B ob (encodeBTNInstance desc G S P l) (residue f l q hf (s.value hf A q α))
        (polyBound k m * T * (2:ℝ)^((k:ℝ)*S/Real.sqrt (D3Stopped.level S : ℝ))) (polyBound k m) := by sorry
