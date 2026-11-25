-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_stepper_copy_v4
-- name    : DetDLP.scalar_contraction_local_stepper_copy_v4
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T03:59:38.491794+00:00
-- url     : https://prove2.me/theorems/79e0d7e6-7d8b-49d6-b2ae-e74d52bf2f5b
-- title:
--   Context stepper with a linear step bound
-- statement:
--   For every positive number of context stacks there is one stepper that copies a stored answer. If context slot $0$ equals $\mathrm{answer}.\mathrm{bits}$ and $\mathrm{answer}<B$, then on every legal frame the stepper returns that value. The number of steps is at most $100(|\mathrm{answer}.\mathrm{bits}|+1)$. Throughout the run, every stack has length at most the longest context stack, plus the bit length of $q^{\mathrm{depth}+1}$, plus $4$, where $q=B+1$.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026, Section 5.2. Corrected local-instruction packaging: preparation depends on the port oracle, and the stepper step and stack bounds are existential and linear in the answer length.

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- Copy the context-backed answer onto the return frame in linear bit-length. -/
theorem scalar_contraction_local_stepper_copy_v4
    (s : ℕ) (hs : 0 < s) :
    ∃ (lc : ℕ) (stepper : BitProgram.Program 8 (20 + s) lc),
      ∀ (answer B depth : ℕ) (context : Fin s → List Bool),
        0 < B → answer < B → context ⟨0, hs⟩ = answer.bits →
        let M := (List.ofFn (fun i => (context i).length)).foldl Nat.max 0
        let F : ℕ → ℕ → Answer := fun _ _ => .value answer
        let q := B + 1
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let small (z : Answer) := match z with
          | .value v => v < B
          | .call a b => a < B ∧ b < B
        let returned (a b stack : ℕ) (z : Answer) := match z with
          | .value v => pack a b stack 0 v 0
          | .call save child => pack a b stack 1 child save
        ∃ (T U : ℕ),
          (∀ i, (context i).length ≤ U) ∧
          T ≤ 100 * (answer.bits.length + 1) ∧
          U ≤ M + ((q ^ (depth + 1)).bits.length) + 4 ∧
          ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
            a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
            let start : BitProgram.Cfg 8 (20 + s) lc :=
              ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
            ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
              BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
              ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
                ∀ i, (c.stacks i).length ≤ U := by sorry

end DetDLP
