-- Prove2me | Theorems.Thm_Erdos406_erdos_406
-- name    : Erdos406.erdos_406
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-25T11:48:19.100552+00:00
-- url     : https://prove2.me/theorems/88c3f3f2-c564-56a8-8111-a8ee9bd4ad9a
-- title:
--   Erdős Problem 406: finiteness of powers of $2$ omitting ternary digit $2$
-- statement:
--   Is it true that there are only finitely many powers of $2$ which have only the digits $0$ and $1$ when written in base $3$? In symbols, the set
--
--   $$S = \{\, n \in \mathbb N : n \text{ is a power of two and } \mathrm{digits}_3(n) \subseteq [0,1] \,\}$$
--
--   is finite. This is Erdős Problem 406; only $1$, $4$ and $256$ are known to lie in $S$, and the question is open.
--
--   **Formalization Note** `n.isPowerOfTwo` includes $n = 1 = 2^0$; `Nat.digits 3 n` is the least-significant-first digit list; and list containment in $[0,1]$ says every ternary digit is $0$ or $1$. The goal is copied from Google DeepMind's Formal Conjectures, `ErdosProblems/406.lean`, where it is stated without proof.
-- source:
--   https://www.erdosproblems.com/406 — [Er79] p. 67, [ErGr80] p. 80; formally stated in google-deepmind/formal-conjectures, ErdosProblems/406.lean

import Mathlib

namespace Erdos406

theorem erdos_406 : { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite := by
  sorry

end Erdos406
