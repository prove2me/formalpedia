-- Prove2me | Theorems.Thm_DetDLP_bounded_entry_evaluator_stack_simulation
-- name    : DetDLP.bounded_entry_evaluator_stack_simulation
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T15:53:52.966301+00:00
-- url     : https://prove2.me/theorems/63be7757-b402-43ae-b36a-cc0f00505fa5
-- title:
--   Bounded Boolean-stack simulation of an arbitrary tensor entry evaluator
-- statement:
--   For any deterministic multitape primitive evaluator E and output tape, one finite three-register Boolean-stack program simulates every run whose input begins with true, the prefix of all framed tensor queries. Its input stacks contain the remaining input bits and their presence flags. From arbitrary register values, it halts within eight source instructions per evaluator step. Every intermediate stack uses at most the original space bound plus eight bits. The output word is recovered from two designated stacks by reading successive values while their presence flags are true. All other start stacks are empty.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Executable entry-evaluation interface for the scalar recursion in Section 5.2 and the residual calls in Section 5.3.

import Definitions.Def_DetDLP_Machine
import Definitions.Def_OAIQ081S000

set_option autoImplicit false
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open BitProgram

namespace DetDLP

theorem bounded_entry_evaluator_stack_simulation (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l : ℕ) (Q : Program 3 s l) (it iv ot ov : Fin s), it≠iv ∧ ot≠ov ∧
    ∀ (input output : List Bool) (T M : ℝ),RunsWithin E out (true::input) output T M →
      ∀ r : Fin 3→Bool,
      let initial : Cfg 3 s l := ⟨some Q.entry,r,fun j =>
        if j=it then List.replicate input.length true else if j=iv then input else []⟩
      ∃ (n : ℕ) (final : Cfg 3 s l), (n:ℝ)≤8*T ∧ BitProgram.Trace Q n initial final ∧
        final.pc=none ∧ ((((final.stacks ot).zip (final.stacks ov)).takeWhile Prod.fst).map Prod.snd)=output ∧
        ∀ k c,k≤n→ BitProgram.Trace Q k initial c→∀ j,(c.stacks j).length≤⌊M⌋₊+8 := by sorry

end DetDLP
