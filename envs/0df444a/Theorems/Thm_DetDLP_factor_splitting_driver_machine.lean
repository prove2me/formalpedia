-- Prove2me | Theorems.Thm_DetDLP_factor_splitting_driver_machine
-- name    : DetDLP.factor_splitting_driver_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:46:35.071817+00:00
-- url     : https://prove2.me/theorems/36abfd8b-bd9e-4f96-9e1b-356640b95765
-- title:
--   Resource-bounded driver for recursive divisor splitting
-- statement:
--   Given a deterministic subroutine f with the stated divisor-search time and space bounds, there is a uniform machine for the following computation on a binary integer N≥2. At most n=⌈log₂(N+1)⌉ levels are used. At a node x, test whether f(x) is a proper divisor. If so, split x into f(x) and x/f(x). Stop at a failed test or at the depth limit. Return all leaf labels in nondecreasing order using the prime-list encoding. The driver has time 2 to the power K n / √log₂(n) and polynomial space. The specification makes no primality or success assumption on the subroutine.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 2.6, pp. 10–11.

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem factor_splitting_driver_machine
    (f : ℕ → ℕ) (Md : PrimitiveMachine) (od : Fin Md.tapeCount) (Kd : ℕ)
    (hd : ∀ N : ℕ, 2 ≤ N →
      let n := bitLen (N+1)
      RunsWithin Md od (countWord N) (countWord (f N))
        ((2 : ℝ)^((Kd : ℝ)*n/Real.sqrt (logSafe n))) (polyBound Kd n)) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N+1)
        let split : ℕ → ℕ → List ℕ :=
          Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
            let d := f x
            if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x/d) else [x])
        RunsWithin M out (countWord N) (encodeNatListBin ((split n N).mergeSort))
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n) := by sorry

end DetDLP
