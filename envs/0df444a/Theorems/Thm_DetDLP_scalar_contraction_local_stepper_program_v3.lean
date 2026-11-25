-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_stepper_program_v3
-- name    : DetDLP.scalar_contraction_local_stepper_program_v3
-- status  : Disproved
-- author  : @Bingsheng
-- created : 2026-11-25T00:48:30.021539+00:00
-- url     : https://prove2.me/theorems/e98fd4d6-ddf0-4343-829a-4b260f6869fd
-- title:
--   Context-backed stepper (existential T)
-- statement:
--   Sound stepper leaf with answer from context and existential T.
-- source:
--   DetDLP

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem scalar_contraction_local_stepper_program_v3
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov)
    (s : ℕ) (hs : 0 < s) :
    ∃ (lc : ℕ) (stepper : BitProgram.Program 8 (20 + s) lc),
      ∀ (answer B U depth x y : ℕ) (context : Fin s → List Bool),
        0 < B → answer < B → context ⟨0, hs⟩ = answer.bits →
        (∀ i, (context i).length ≤ U) →
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
        ∃ T : ℕ,
          ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
            a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
            let start : BitProgram.Cfg 8 (20 + s) lc :=
              ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
            ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
              BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
              ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
                ∀ i, (c.stacks i).length ≤ U := by sorry

end DetDLP
