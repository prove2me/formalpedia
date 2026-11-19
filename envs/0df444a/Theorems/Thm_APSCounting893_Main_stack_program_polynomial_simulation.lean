-- Prove2me | Theorems.Thm_APSCounting893_Main_stack_program_polynomial_simulation
-- name    : APSCounting893.Main.stack_program_polynomial_simulation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:17:42.28456+00:00
-- url     : https://prove2.me/theorems/3eff9a9d-577d-4ae7-879a-08d184603ded
-- title:
--   Polynomial simulation of finite register oracle programs
-- statement:
--   Let $Q$ be a finite control set and let $r+2$ be a fixed number of word registers. Let $P$ be a register program, $A$ an oracle language and $L$ a language. Suppose there are constants $c,d$ such that, on every input word $x$ and with an empty auxiliary word, the program halts correctly within the common clock $c(|x|+1)^d$. Then
--
--   $$L\in P^A.$$
--
--   The conclusion uses ordinary finite oracle machines. It permits reuse of verified register algorithms without taking register operations as a separate complexity model.
-- source:
--   Auxiliary finite-machine proof component for Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.5, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives

set_option autoImplicit false

theorem APSCounting893.Main.stack_program_polynomial_simulation
    {Q : Type} [Fintype Q] {r : ℕ} (P : APSCounting893.Main.StackProgram Q r)
    (A L : APSCounting893.Main.Language) (c d : ℕ)
    (h : ∀ x : APSCounting893.Main.Word, ∃ answer : Bool,
      (P.run A x [] (APSCounting893.Main.polyBound c d x.length)).answer = some answer ∧
        (answer = true ↔ L x)) : APSCounting893.Main.InOracleP A L := by sorry
