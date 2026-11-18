-- Prove2me | Theorems.Thm_EditGV897_Main_constructor_program
-- name    : EditGV897.Main.constructor_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:34:58.481718+00:00
-- url     : https://prove2.me/theorems/1442d61f-8ed0-441c-afe2-4a125f3b5ddc
-- title:
--   Uniform finite-program construction of shared parameters
-- statement:
--   For every fixed edit budget $t$, a fixed finite binary tape program computes the specified shared parameters for every block length $n$. There are natural constants $A>0,d$ such that the actual execution and the encoded parameter length are bounded by
--
--   $$A(n+1)^d.$$
--
--   The output contains the prescribed parity rows and syndrome, with the specified serialization. This is the deterministic setup component of the source's complete construction.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, Theorem 1 and §4 main proof, printed pp.5,13 / PDF pp.6,14. Operational implementation interface for the specified setup and codec algorithms.

import Definitions.Def_EditGV897_Main_Codec
open EditGV897.Main

theorem EditGV897.Main.constructor_program (t : ℕ) :
    ∃ (constructor : Program) (A d : ℕ), 0 < A ∧ ∀ n : ℕ,
      (parametersCode (setup t n)).length ≤ polyBudget A d n ∧
      Runs constructor (unary n) (parametersCode (setup t n)) (polyBudget A d n) := by sorry
