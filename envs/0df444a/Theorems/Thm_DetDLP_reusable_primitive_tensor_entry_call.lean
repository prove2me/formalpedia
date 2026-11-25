-- Prove2me | Theorems.Thm_DetDLP_reusable_primitive_tensor_entry_call
-- name    : DetDLP.reusable_primitive_tensor_entry_call
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T18:29:02.789728+00:00
-- url     : https://prove2.me/theorems/8d3e6b64-c195-45e7-b83e-ead3507dae11
-- title:
--   A reusable stack call for the primitive tensor-entry evaluator
-- statement:
--   Compile an arbitrary deterministic multitape entry evaluator into a finite Boolean-stack subroutine. From separate description, vertex, and port-bit words, the subroutine builds the canonical query, calls the evaluator, and returns its exact output word, clearing every other stack. If the primitive run has time T and space U, then the resulting time is at most 8T plus linear overhead in the input lengths and U. Every prefix uses at most that same overhead per stack, independently of T.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Lemma 5.2, original tensor-entry instruction and reusable call bound.

import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

namespace DetDLP

theorem reusable_primitive_tensor_entry_call (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l : ℕ) (caller : BitProgram.Program 8 (s+3) l) (src : Fin s),
      ∀ (desc : List Bool) (v : ℕ) (bits word : List Bool) (T U : ℕ),
      RunsWithin E out (encodePortQuery desc v bits) word T U →
      ∀ r : Fin 8→Bool,
      let vert := SqrtLogSpace.countWord v
      let V := (s+4)*(20*(desc.length+vert.length+bits.length+(U+8)+10))
      let input := Fin.addCases (m:=s) (n:=3) (fun j => if j=src then desc else []) ![vert,bits,[]]
      let output := Fin.addCases (m:=s) (n:=3) (fun _ => ([]:List Bool)) ![word,[],[]]
      let start : BitProgram.Cfg 8 (s+3) l := ⟨some caller.entry,r,input⟩
      ∃ steps rf,steps ≤ 8*T+V ∧ BitProgram.Trace caller steps start ⟨none,rf,output⟩ ∧
        ∀ j c,j ≤ steps → BitProgram.Trace caller j start c → ∀ i,(c.stacks i).length ≤ V := by sorry
end DetDLP
