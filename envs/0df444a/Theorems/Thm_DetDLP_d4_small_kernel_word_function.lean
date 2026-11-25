-- Prove2me | Theorems.Thm_DetDLP_d4_small_kernel_word_function
-- name    : DetDLP.d4_small_kernel_word_function
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T06:17:01.572685+00:00
-- url     : https://prove2.me/theorems/7954d27b-31cd-46cd-bbf7-db6517396aa8
-- title:
--   Word interface to the small contraction kernel
-- statement:
--   The bounded exhaustive contraction kernel induces a polynomial-time function on a stack-word bank and a unary clock. On its prescribed initial bank it returns the packed contraction integer, whose successive digits give the terminal coefficients.

import Definitions.Def_DetDLP_D4Plan
import Definitions.Def_ToTuring_PolyT
set_option autoImplicit false
open Groundwork DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_small_kernel_word_function (C c L : ℕ) (E : PrimitiveMachine) (oe : Fin E.tapeCount) :
    ∃ (s K : ℕ) (sim : List (List Bool) × List Bool → List Bool), PolyT sim ∧
    ∀ x : Input C c, Nat.clog 2 x.S < L → entry x E oe →
      let r := x.G.nV+3
      let pairs := (List.finRange x.G.nE).map fun e => ((x.G.endpoints e).1.val,(x.G.endpoints e).2.val)
      let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2])+r^(2*pairs.length)
      let w := x.G.nE+x.G.nV*(x.p+Nat.clog 2 x.l)+1+x.p
      let B := 2^w
      let bank := List.replicate 8 ([] : List Bool) ++ [(2^x.G.nE : ℕ).bits,x.G.nV.bits,[],[],(1:ℕ).bits,[],[],[],(1:ℕ).bits,(1:ℕ).bits,(2^x.G.nE:ℕ).bits] ++
        [x.desc,r.bits,code.bits,(code/r).bits,(B-1).bits,B.bits,(B-1-2).bits] ++ List.replicate s []
      ∀ fuel : List Bool, K*(size x+1)^K ≤ fuel.length → ∃ z : ℕ, sim (bank,fuel) = z.bits ∧
        encodeNatListBin (List.ofFn fun i : Fin x.l => z/B^i.val%B%(2^x.p)) = answer x := by sorry
