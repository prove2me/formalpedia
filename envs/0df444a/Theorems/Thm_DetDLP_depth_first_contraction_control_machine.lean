-- Prove2me | Theorems.Thm_DetDLP_depth_first_contraction_control_machine
-- name    : DetDLP.depth_first_contraction_control_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T17:36:24.372593+00:00
-- url     : https://prove2.me/theorems/83292976-f41f-433f-942d-1e108d5b94e4
-- title:
--   Finite Boolean-stack control for depth-first contraction with bounded continuations
-- statement:
--   Given any finite local program returning either a value or a child with a continuation, construct a finite Boolean-stack evaluator for arbitrary adaptive sequential recursion. A request computes its child and resumes the saved parent with the resulting value. Any extra context stacks are restored at every local call. The number of actual steps is linear in the number of calls times their cost plus a polynomial in frame width and maximum pending depth. The bound on every intermediate stack is the maximum of local workspace and this control overhead, independent of the number of calls.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Sections 5.2–5.3, bounded-space depth-first traversal for scalar contraction and on-demand terminal factors.

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_OAIQ081S000

set_option autoImplicit false
open OAI.Algorithms.SubexponentialSAT DetDLP.ContinuationSchedule

namespace DetDLP

theorem depth_first_contraction_control_machine {s l : ℕ} (Q : BitProgram.Program 8 (20+s) l) :
    ∃ (labels L : ℕ) (M : BitProgram.Program 8 (20+s) labels),∀ (context : Fin s→List Bool)
      (F : ℕ→ℕ→Answer) (B T U : ℕ) (x y value calls depth : ℕ),
      0<B → (∀ i,(context i).length≤U) → Computes F B x y value calls depth →
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
      (∀ (a b stack : ℕ) (r : Fin 8→Bool),a<B → b<B → stack < q^(depth+1) → small (F a b) →
        let start : BitProgram.Cfg 8 (20+s) l := ⟨some Q.entry,r,pack a b stack 0 0 0⟩
        ∃ (steps : ℕ) (r' : Fin 8→Bool),steps≤T ∧
          BitProgram.Trace Q steps start ⟨none,r',returned a b stack (F a b)⟩ ∧
          ∀ j c,j≤ steps → BitProgram.Trace Q j start c → ∀ i,(c.stacks i).length≤U) →
      ∀ (r : Fin 8→Bool),r 1=true →
      let start : BitProgram.Cfg 8 (20+s) labels := ⟨some M.entry,r,pack x y 1 0 0 0⟩
      let overhead := L*(q.size*(depth+1)+3)^2
      ∃ (steps : ℕ) (rf : Fin 8→Bool),steps≤2+calls*(1+T+overhead) ∧
        BitProgram.Trace M steps start ⟨none,rf,pack 1 value 0 0 0 0⟩ ∧
        ∀ j c,j≤ steps → BitProgram.Trace M j start c → ∀ i,(c.stacks i).length ≤ max U overhead := by sorry
end DetDLP
