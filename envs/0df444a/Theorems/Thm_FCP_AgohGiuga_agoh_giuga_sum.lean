-- Prove2me | Theorems.Thm_FCP_AgohGiuga_agoh_giuga_sum
-- name    : FCP.AgohGiuga.agoh_giuga_sum
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:22:50.514646+00:00
-- url     : https://prove2.me/theorems/fed61a57-44dd-4fab-9974-281eebac7d03
-- title:
--   Agoh--Giuga conjecture (Giuga's formulation)
-- statement:
--   **Giuga's conjecture.** For every integer $p \ge 2$,
--   $$p \text{ is prime} \iff p \;\Big|\; 1 + \sum_{i=1}^{p-1} i^{\,p-1}.$$
--
--   The forward implication is Fermat's little theorem; the content of the conjecture is the converse, i.e. that no composite number satisfies the congruence $\sum_{i=1}^{n-1} i^{\,n-1} \equiv -1 \pmod n$. Such a composite counterexample would be a Carmichael number and a Giuga number simultaneously, and is known to have more than $13{,}000$ digits.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/AgohGiuga.lean); https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture

import Mathlib

namespace FCP.AgohGiuga

theorem agoh_giuga_sum (p : ℕ) (hp : 2 ≤ p) :
    p.Prime ↔ p ∣ 1 + ∑ i ∈ Finset.Ioo 0 p, i ^ (p - 1) := by sorry

end FCP.AgohGiuga
