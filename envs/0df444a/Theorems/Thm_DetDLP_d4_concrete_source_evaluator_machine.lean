-- Prove2me | Theorems.Thm_DetDLP_d4_concrete_source_evaluator_machine
-- name    : DetDLP.d4_concrete_source_evaluator_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:23:09.216047+00:00
-- url     : https://prove2.me/theorems/8a2c13aa-2ac7-4bf5-8ca1-c18acb6249f8
-- title:
--   Uniform machine for concrete lookup and stopped-source queries
-- statement:
--   For fixed original-entry and packet evaluators, one machine answers both concrete source queries under the closed contraction hypothesis. A lookup restores the original index and pads coefficients. For a stopped core the machine contracts the graph after pinning the open bits. Writing $L=\lceil\log_2 S\rceil$, its time is bounded by a polynomial in the charged input size times $2^{K S/\sqrt{L}}$, and its workspace is polynomial. The packet size is polynomial in $S$ alone.

import Definitions.Def_DetDLP_D4StoppedNode
set_option autoImplicit false
open DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode Polynomial
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.d4_concrete_source_evaluator_machine (hClosed : AppendixD4.Closed)
    (C c K_pkt c_pkt : ℕ) (hC : 0 < C) (E F : PrimitiveMachine)
    (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (K L₀ : ℕ),
    (∀ (S κ l q : ℕ) (origDesc : Bits) (R origG : Graph) (v : Fin R.nV) (j : Fin origG.nV)
      (α : Fin (origG.deg j) → Bool) (V : Tensor origG (Fin l → ℕ)) (f : ℤ[X]) (hf : f.Monic),
      let N := S+origDesc.length
      let u := encodePortQuery (lookupDesc origDesc j.val κ l q) v.val (List.ofFn α)
      let x := encodePortQuery origDesc j.val (List.ofFn α)
      let a := V j α
      let y := encodeNatListBin (List.ofFn a)
      κ = f.natDegree → κ ≤ u.length → (∀ t, a t < 2^q) →
      u.length ≤ c*(N+1)^c → x.length ≤ c*(N+1)^c → y.length ≤ c*(N+1)^c →
      RunsWithin E oE x y (polyBound c N) (polyBound c N) →
      RunsWithin B ob u (residue f l q hf (liftBase f l q a))
        (polyBound K N * (2:ℝ)^((K:ℝ)*S/Real.sqrt (D3Stopped.level S:ℝ))) (polyBound K N)) ∧
    (∀ (S P q l d₀ deg i : ℕ) (origDesc : Bits) (origG G_stop : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G_stop f l P deg) (V : Tensor origG (Fin l → ℕ)) (α : Fin deg → Bool),
      let N := S+origDesc.length
      let n := S+(s.payload origDesc α).length
      let desc := D3Stopped.descOf d₀ f (s.payload origDesc α)
      let m := S+desc.length
      let u := encodePortQuery (stoppedDesc origDesc S l P d₀ f G_stop s.tableBits) i (List.ofFn α)
      let x := encodeBTNInstance desc G_stop S P l
      let y := residue f l P hf (BTNContract G_stop (s.entry hf V α))
      L₀ ≤ D3Stopped.level S → D3Stopped.shift S (d₀-1) ≤ D3Stopped.level S / 32768 →
      G_stop.nE ≤ C*S/8^d₀ → G_stop.maxDeg ≤ D3Stopped.cap S → G_stop.nV ≤ (m+1)^c →
      1 ≤ P → P ≤ S+80*C*S*(if d₀=0 then 1 else 2^D3Stopped.shift S (d₀-1)) →
      1 ≤ l → l ≤ C*S → RingOK f → f.natDegree = 4*D3Stopped.level S → P ≤ q →
      (∀ v t j, V v t j < 2^P) → u.length ≤ c*(N+1)^c → x.length ≤ c*(N+1)^c → y.length ≤ c*(N+1)^c →
      (∀ (w : Fin G_stop.nV) (β : Fin (G_stop.deg w) → Bool),
        (encodePortQuery desc w.val (List.ofFn β)).length ≤ c*(n+1)^c) →
      (∀ v t, let inp := encodePortQuery origDesc v.val (List.ofFn t)
              let ans := encodeNatListBin (List.ofFn (V v t))
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧
              RunsWithin E oE inp ans (polyBound c n) (polyBound c n)) →
      (∀ w pkt (h : s.vTable w = .pkt pkt) β, let p := s.packet w pkt h
              let n_pkt := G_stop.nE+p.creation+4*D3Stopped.level S+l+2
              let inp := Encoding.encodeList id [pkt,List.ofFn β]
              let ans := residue f l p.creation hf (p.entry β)
              n_pkt ≤ (S+2)^c_pkt ∧ inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧
              RunsWithin F oF inp ans (Real.exp ((K_pkt:ℝ)*(2^D3Stopped.shift S (d₀-1):ℕ)*Real.log n_pkt))
                (polyBound K_pkt n_pkt)) →
      RunsWithin B ob u (residue f l q hf (s.value hf V q α))
        (polyBound K N * (2:ℝ)^((K:ℝ)*S/Real.sqrt (D3Stopped.level S:ℝ))) (polyBound K N)) := by sorry
