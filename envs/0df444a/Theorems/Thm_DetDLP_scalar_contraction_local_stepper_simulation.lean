-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_stepper_simulation
-- name    : DetDLP.scalar_contraction_local_stepper_simulation
-- status  : Disproved
-- author  : @Bingsheng
-- created : 2026-11-24T09:20:05.999243+00:00
-- url     : https://prove2.me/theorems/9783f138-3251-47e8-8901-ae7739b454f8
-- title:
--   Stepper frame simulation
-- statement:
--   Each bounded local frame is advanced by the stepper within time T and stack U.
-- source:
--   DetDLP Section 5.2

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem scalar_contraction_local_stepper_simulation
    {s lc : ℕ} (stepper : BitProgram.Program 8 (20+s) lc)
    (context : Fin s→List Bool) (F : ℕ→ℕ→Answer) (B T U depth : ℕ)
    (hctx : ∀ i,(context i).length≤U) (hB : 0<B) :
    let q := B+1
    let pack (a b stack tag arg save : ℕ) : Fin (20+s)→List Bool :=
      let v : Fin 12→ℕ := ![q,1,0,a,b,stack,tag,arg,save,0,0,0]
      Fin.addCases (m:=20) (n:=s) (Fin.addCases (m:=8) (n:=12) (fun _ => []) (fun j => (v j).bits)) context
    let small (z : Answer) := match z with
      | .value v => v<B
      | .call a b => a<B ∧ b<B
    let returned (a b stack : ℕ) (z : Answer) := match z with
      | .value v => pack a b stack 0 v 0
      | .call save child => pack a b stack 1 child save
    ∀ (a b stack : ℕ) (r : Fin 8→Bool),a<B → b<B → stack < q^(depth+1) → small (F a b) →
      let start : BitProgram.Cfg 8 (20+s) lc := ⟨some stepper.entry,r,pack a b stack 0 0 0⟩
      ∃ (steps : ℕ) (r' : Fin 8→Bool),steps≤T ∧
        BitProgram.Trace stepper steps start ⟨none,r',returned a b stack (F a b)⟩ ∧
        ∀ j c,j≤ steps → BitProgram.Trace stepper j start c → ∀ i,(c.stacks i).length≤U := by sorry

end DetDLP
