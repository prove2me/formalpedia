-- Prove2me | Theorems.Thm_DetDLP_D3Stopped_d3_stopped_core_continuation_machine
-- name    : DetDLP.D3Stopped.d3_stopped_core_continuation_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T07:16:15.397021+00:00
-- url     : https://prove2.me/theorems/ec5dd50e-c444-49ca-aafe-383fabd40297
-- title:
--   Stopped-core continuation by a uniform contraction machine
-- statement:
--   Assuming the closed-schedule contraction theorem, a single primitive machine contracts every valid stopped-core instance at sufficiently large scale. It returns the canonical residue of the contraction using polynomial space in the scale plus descriptor length. Its time bound is polynomial in that size, linear in the supplied entry-evaluation time, and exponential only in the scale divided by the square root of its ceiling binary logarithm.

import Definitions.Def_DetDLP_D3StoppedRaw
set_option autoImplicit false

namespace DetDLP.D3Stopped
open Polynomial AppendixD4 OAI.Algorithms.SubexponentialSAT.Computation
theorem d3_stopped_core_continuation_machine
    (hClosed : AppendixD4.Closed) (C c : ℕ) (hC : 0 < C) (hc : 0 < c)
    (E : PrimitiveMachine) (oE : Fin E.tapeCount) :
    ∃ (A : PrimitiveMachine) (oA : Fin A.tapeCount) (K L₀ : ℕ),
      ∀ (S P l Told d₀ : ℕ) (payload : Bits) (G : Graph) (f : ℤ[X]) (hf : f.Monic)
        (T : Tensor G (ResidualScalarOracle.B f l P)),
        let desc := descOf d₀ f payload
        L₀ ≤ level S → 1 ≤ Told → G.nE ≤ C*S/8^d₀ → G.maxDeg ≤ cap S →
        G.nV ≤ (S+desc.length+1)^c → 1 ≤ P →
        P ≤ S+80*C*S*(if d₀=0 then 1 else 2^shift S (d₀-1)) →
        1 ≤ l → l ≤ C*S → RingOK f → f.natDegree = 4*level S →
        (∀ v α, RunsWithin E oE (encodePortQuery desc v.val (List.ofFn α))
          (residue f l P hf (T v α)) Told (((S+desc.length : ℕ) : ℝ)^c)) →
        RunsWithin A oA (encodeBTNInstance desc G S P l) (residue f l P hf (BTNContract G T))
          (polyBound K (S+desc.length)*(Told : ℝ)*(2:ℝ)^((K:ℝ)*(S:ℝ)/Real.sqrt (level S : ℝ)))
          (polyBound K (S+desc.length)) := by sorry
end DetDLP.D3Stopped
