-- Prove2me | Theorems.Thm_APSCounting893_Main_stack_function_polynomial_simulation
-- name    : APSCounting893.Main.stack_function_polynomial_simulation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:37:21.120267+00:00
-- url     : https://prove2.me/theorems/0e0f4893-617c-4443-b3ad-9a2f664378c9
-- title:
--   Polynomial simulation of stack programs with physical word output
-- statement:
--   Let $A$ be a language and $f$ a total function on binary words. Fix one finite stack program, a designated stop state, and an output register. Each instruction pops or pushes one bit, branches on a stack, or queries the word written in a register. Suppose the stop state halts with answer true, and there are constants $c,d$ such that on every input $x$ the program reaches that state, before halting, within $c(|x|+1)^d$ stack steps with $f(x)$ in the selected register. Then
--
--   $$f\in\mathrm{FP}^{A}.$$
--
--   The conclusion uses an ordinary finite oracle machine with physical tapes: the returned word is read from its charged output tape. The finite transition table, time polynomial and selected register are independent of the input. This simulation supplies word-valued subroutines for the dimension and coefficient algorithms in Section 6.
-- source:
--   Implementation lemma for the uniform finite oracle-machine model in Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Section 6, Lemma 6.1 (p. 23), Theorem 6.4 and Theorem 1.3 proof (pp. 25–26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.stack_function_polynomial_simulation {Q : Type} [Fintype Q] {r : ℕ}
    (P : StackProgram Q r) (A : Language) (f : Word → Word)
    (stop : Q) (src : Fin (r+2)) (hstop : P.transition stop=.halt true) (c d : ℕ)
    (h : ∀ x : Word,∃ T≤polyBound c d x.length,
      (P.run A x [] T).state=stop ∧ (P.run A x [] T).answer=none ∧ (P.run A x [] T).regs src=f x) :
    FunctionInPWithOracle A f := by sorry
