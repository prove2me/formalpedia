-- Prove2me | Theorems.Thm_FamousTheorems_halting_problem_undecidable
-- name    : FamousTheorems.halting_problem_undecidable
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:25.104731+00:00
-- url     : https://prove2.me/theorems/8bd2345e-e079-4e49-8a2e-5b6c3b7c55cc
-- title:
--   The undecidability of the halting problem
-- statement:
--   **The undecidability of the halting problem.** Fix an input $n\in\mathbb N$. There is no computable procedure that decides, given a program $c$, whether $c$ halts on input $n$.
--
--   This is Turing's theorem, the founding result of computability theory. Most other undecidability results, from Hilbert's tenth problem to the word problem for groups, are proved by reduction to it, and it underlies Gödel-type incompleteness phenomena.
--
--   **Formalization note.** Mathlib's `ComputablePred.halting_problem`. Programs are codes `Nat.Partrec.Code` for partial recursive functions, `c.eval n` is the (partial) result of running `c` on `n`, and `.Dom` says it is defined, i.e. the computation halts. `ComputablePred` means the predicate is decidable by a computable function.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ComputablePred.halting_problem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem halting_problem_undecidable (n : ℕ) : ¬ComputablePred fun c : Nat.Partrec.Code => (c.eval n).Dom := by sorry

end FamousTheorems
