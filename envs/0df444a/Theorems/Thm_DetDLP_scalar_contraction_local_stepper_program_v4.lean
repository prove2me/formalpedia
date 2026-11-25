-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_stepper_program_v4
-- name    : DetDLP.scalar_contraction_local_stepper_program_v4
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T04:05:34.547239+00:00
-- url     : https://prove2.me/theorems/34a58f1a-5abb-4870-98bc-d552e9214628
-- title:
--   Frame-sized stepper for a context answer
-- statement:
--   For every positive context width there is one stepper which copies a context-backed constant answer onto the return frame.
--
--   Fix a bound $B>0$, a depth, and a context whose first slot is $\mathrm{answer}.\mathsf{bits}$ for some $\mathrm{answer}<B$. The stepper, on every call $(a,b,\mathrm{stack})$ inside the continuation range, starts from the packed frame with tag and saved argument equal to $0$ and halts in the frame that writes $\mathrm{answer}$ into the argument slot. One step bound $T$ works for every such call.
--
--   The stack cap $U$ is chosen after $B$, the depth, and the context. It dominates every context stack and every stack of the packed frame. In particular it is large enough for the constant bit-list $(1).\mathsf{bits}$ stored on stack $9$. A cap supplied only by the context, such as $U=0$ when the answer is $0$, is not the cap used here.
-- source:
--   DetDLP Lemma 5.2 / Theorem 3.1, private mission correction of the local instruction packaging

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- Copy a context-backed constant answer onto the return frame. The stack cap `U`
is chosen after `B` and `depth`, so it may exceed the context length. The packed
frame always stores `(1).bits` on stack 9, which rules out a context-only cap
such as `U = 0`. -/
theorem scalar_contraction_local_stepper_program_v4
    (s : ℕ) (hs : 0 < s) :
    ∃ (lc : ℕ) (stepper : BitProgram.Program 8 (20 + s) lc),
      ∀ (answer B depth : ℕ) (context : Fin s → List Bool),
        0 < B → answer < B → context ⟨0, hs⟩ = answer.bits →
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
          ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
            a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
            let start : BitProgram.Cfg 8 (20 + s) lc :=
              ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
            ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
              BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
              ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
                ∀ i, (c.stacks i).length ≤ U := by sorry

end DetDLP
