-- Prove2me | Theorems.Thm_FCP_Mills_mills_constant_irrational
-- name    : FCP.Mills.mills_constant_irrational
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:49:30.186977+00:00
-- url     : https://prove2.me/theorems/b1ccb598-668f-4479-8ac7-c08443d865d9
-- title:
--   Mills' constant is irrational (Saito, 2024)
-- statement:
--   **Saito's theorem (2024).** Mills' constant — the least real $A > 1$ such that $\lfloor A^{3^n}\rfloor$ is prime for all $n \ge 1$ — is irrational. The statement is formulated for an arbitrary $A$ that is a least element of the set of Mills numbers greater than $1$, so it does not presuppose the existence of that least element.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Mills.lean); K. Saito, Mills' constant is irrational, Mathematika 71 (2025), e70027, arXiv:2404.19461

import Mathlib
import Definitions.Def_FCP_Mills

namespace FCP.Mills

theorem mills_constant_irrational (A : ℝ) (hA : IsMinMills A) : Irrational A := by sorry

end FCP.Mills
