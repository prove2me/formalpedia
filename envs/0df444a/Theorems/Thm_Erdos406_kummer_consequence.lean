-- Prove2me | Theorems.Thm_Erdos406_kummer_consequence
-- name    : Erdos406.kummer_consequence
-- status  : Proved
-- author  : @loader3229
-- created : 2026-11-25T11:42:50.507137+00:00
-- url     : https://prove2.me/theorems/7cfad7d9-b6db-4741-82e4-3dadffea0af2
-- title:
--   Kummer consequence: $3 \mid \binom{2^{k+1}}{2^k}$ eventually
-- statement:
--   An affirmative answer to Erdős Problem 406 would imply, via Kummer's theorem, that
--
--   $$3 \mid \binom{2^{k+1}}{2^k} \qquad \text{for all sufficiently large } k .$$
--
--   The implication makes the digit question contact divisibility properties of binomial coefficients.
--
--   **Formalization Note** The finiteness of the digit-restricted set of powers of two is kept as a hypothesis $h$, since the source states the divisibility as a consequence of the conjecture and not as an unconditional result; the eventually quantifier with the `atTop` filter encodes 'for all sufficiently large $k$'.
-- source:
--   https://www.erdosproblems.com/406 — third paragraph of the problem statement (Kummer's theorem)

import Mathlib

namespace Erdos406

theorem kummer_consequence
    (h : { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite) :
    ∀ᶠ k : ℕ in Filter.atTop, 3 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
  sorry

end Erdos406
