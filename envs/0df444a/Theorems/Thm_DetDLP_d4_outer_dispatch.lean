-- Prove2me | Theorems.Thm_DetDLP_d4_outer_dispatch
-- name    : DetDLP.d4_outer_dispatch
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:15:38.092108+00:00
-- url     : https://prove2.me/theorems/e2fde617-9005-417c-93e6-7e2819f295b7
-- title:
--   One dispatcher for lookup and stopped-source descriptors
-- statement:
--   Fix machines for original entries and pinned contractions. One machine selects the indicated call, preserves its query, and converts the reply to the requested coefficient encoding. If the query, call, reply and workspace fit polynomial envelopes at scale $n$, then time is polynomial in $n$ times the call time, and space is polynomial in $n$. Lookup width must fit the saved query.

import Definitions.Def_DetDLP_D4StoppedNode
set_option autoImplicit false
open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.d4_outer_dispatch (E A : PrimitiveMachine) (oE : Fin E.tapeCount) (oA : Fin A.tapeCount) (c : ℕ) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ),
    (∀ (n i v κ l q : ℕ) (origDesc β : Bits) (f : ℤ[X]) (hf : f.Monic) (a : Fin l → ℕ) (τ : ℝ),
      let u := encodePortQuery (lookupDesc origDesc v κ l q) i β
      let x := encodePortQuery origDesc v β
      let ans := encodeNatListBin (List.ofFn a)
      κ = f.natDegree → κ ≤ u.length → 1 ≤ τ → (∀ j, a j < 2^q) →
      u.length ≤ c*(n+1)^c → x.length ≤ c*(n+1)^c → ans.length ≤ c*(n+1)^c →
      RunsWithin E oE x ans τ (polyBound c n) →
      RunsWithin B ob u (residue f l q hf (liftBase f l q a)) (polyBound k n * τ) (polyBound k n)) ∧
    (∀ (n i S P q l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (V : Tensor origG (Fin l → ℕ)) (α : Fin deg → Bool) (τ : ℝ),
      let u := encodePortQuery (stoppedDesc origDesc S l P d f G s.tableBits) i (List.ofFn α)
      let x := encodeBTNInstance (D3Stopped.descOf d f (s.payload origDesc α)) G S P l
      let ans := residue f l P hf (BTNContract G (s.entry hf V α))
      P ≤ q → 1 ≤ τ → u.length ≤ c*(n+1)^c → x.length ≤ c*(n+1)^c → ans.length ≤ c*(n+1)^c →
      RunsWithin A oA x ans τ (polyBound c n) →
      RunsWithin B ob u (residue f l q hf (s.value hf V q α)) (polyBound k n * τ) (polyBound k n)) := by sorry
