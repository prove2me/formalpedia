-- Prove2me | Theorems.Thm_CarmichaelConjecture_carmichael_conjecture
-- name    : CarmichaelConjecture.carmichael_conjecture
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:36.147564+00:00
-- url     : https://prove2.me/theorems/24809f6e-c19e-46ed-aa2f-9d09cc280643
-- title:
--   Carmichael's conjecture: $\varphi$ is never unique
-- statement:
--   For every positive integer $n$ there exists an integer $m\neq n$ such that $\varphi(m)=\varphi(n)$, where $\varphi$ is Euler's totient function. Equivalently, no value of $\varphi$ on the positive integers is assumed exactly once. This is Carmichael's totient-function conjecture, which remains open. The hypothesis $n>0$ is essential: in the natural numbers, $\varphi(0)=0$ has the unique preimage $0$.
-- source:
--   R. D. Carmichael, Note on Euler's φ-function, Bull. Amer. Math. Soc. 28 (1922), 109–110, https://doi.org/10.1090/S0002-9904-1922-03504-5 (conjecture stated after withdrawal of the 1907 argument; lower bound for a unique preimage on p. 110)

import Mathlib

namespace CarmichaelConjecture
theorem carmichael_conjecture {n : Nat} (hn : 0 < n) :
    ∃ m, m ≠ n ∧ Nat.totient m = Nat.totient n := by sorry
end CarmichaelConjecture
