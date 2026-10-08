-- Prove2me | Theorems.Thm_ErdosHeilbronn_erdos_heilbronn
-- name    : ErdosHeilbronn.erdos_heilbronn
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:16:40.573993+00:00
-- url     : https://prove2.me/theorems/e4ec99f7-e3ea-44ff-88d4-736b20bab76e
-- title:
--   Erdős–Heilbronn conjecture, h = 2 (restricted two-fold sumset)
-- statement:
--   Let p be prime and A a nonempty subset of ℤ/p. Then the set of sums a + b of two distinct elements of A has cardinality at least min(p, 2|A| − 3). This is the original h = 2 case of the Erdős–Heilbronn conjecture from 1964, first proved by Dias da Silva and Hamidoune in 1994; it is the restricted analogue of the Cauchy–Davenport theorem, and is sharp for arithmetic progressions.
-- source:
--   P. Erdős, H. Heilbronn, On the addition of residue classes mod p, Acta Arith. 9 (1964); Dias da Silva–Hamidoune (1994); Alon–Nathanson–Ruzsa (1995/96)

import Mathlib

namespace ErdosHeilbronn

/-- The Erdos-Heilbronn conjecture (1964), h = 2 case, proved by Dias da Silva-Hamidoune (1994):
for nonempty `A ⊆ ℤ/p` with `p` prime, the restricted two-fold sumset
`{a + b // a, b ∈ A, a ≠ b}` has at least `min(p, 2|A| - 3)` elements. -/
theorem erdos_heilbronn {p : ℕ} (hp : p.Prime) {A : Finset (ZMod p)} (hA : A.Nonempty) :
    min p (2 * A.card - 3)
      ≤ (((A.product A).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
  sorry

end ErdosHeilbronn
