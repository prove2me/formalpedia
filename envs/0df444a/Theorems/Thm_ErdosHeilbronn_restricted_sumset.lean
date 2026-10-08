-- Prove2me | Theorems.Thm_ErdosHeilbronn_restricted_sumset
-- name    : ErdosHeilbronn.restricted_sumset
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:16:28.16299+00:00
-- url     : https://prove2.me/theorems/b545f500-7024-42c9-9629-1777bb06a5af
-- title:
--   Erdős–Heilbronn restricted sumset theorem (two sets, prime modulus)
-- statement:
--   Let p be prime and let A, B be nonempty subsets of the field ℤ/p. The restricted sumset A ⊎ B = {a + b : a ∈ A, b ∈ B, a ≠ b} satisfies |A ⊎ B| ≥ min(p, |A| + |B| − 3). This is the two-set form of the Erdős–Heilbronn problem: the h = 2 case of the 1964 conjecture was proved by Dias da Silva and Hamidoune (1994) via exterior algebra, and Alon, Nathanson and Ruzsa (1995/96) gave the polynomial-method proof (Combinatorial Nullstellensatz) that this problem's solution follows.
-- source:
--   P. Erdős, H. Heilbronn (1964 conjecture); J. A. Dias da Silva, Y. O. Hamidoune, Bull. London Math. Soc. 26 (1994); N. Alon, M. B. Nathanson, I. Z. Ruzsa, Amer. Math. Monthly 102 (1995) and J. Number Theory 56 (1996)

import Mathlib

namespace ErdosHeilbronn

/-- The two-set Erdos-Heilbronn theorem: for nonempty `A, B ⊆ ℤ/p` with `p` prime,
the restricted sumset `{a + b // a ∈ A, b ∈ B, a ≠ b}` has at least
`min(p, |A| + |B| - 3)` elements. -/
theorem restricted_sumset {p : ℕ} (hp : p.Prime) {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 3)
      ≤ (((A.product B).filter (fun ab => ab.1 ≠ ab.2)).image (fun ab => ab.1 + ab.2)).card := by
  sorry

end ErdosHeilbronn
