-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_Supplement_two_small_orders
-- name    : AnonymousDirectedCounting.Exact.Supplement.two_small_orders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:30.935823+00:00
-- url     : https://prove2.me/theorems/92156c00-7b20-4994-94d5-2897d305bcc9
-- title:
--   Lemma 9 — two small compatible orders
-- statement:
--   Let $\mathcal V$ be an explicit vista with final level $t$ and leader count $\ell$, let $s$ be the binary length of $\langle\mathcal V,\ell\rangle$, $\nu=\sum_{r=0}^t|L_r|$, $M$ the largest of $\ell$, the outdegree labels and the red multiplicities of $\mathcal V$, and
--   $$K=(1+\nu M)^t.$$
--   If $\operatorname{Spec}_\ell(\mathcal V)$ contains two different orders, it contains two different orders that are both at most $K+\ell+2$. Moreover there are constants $C,k$, fixed before every input, such that for every well-formed vista and every $\ell\ge1$ the number $K+\ell+2$ has at most $C(1+s)^k$ binary digits.
--
--   This bound lets a verifier guess two compatible orders of polynomial bit length.
--
--   Differences from the source:
--   - encoding: a realization is a finite network prefix through round t, strongly connected in each round → a network strongly connected in every round (published Admissible); reason: a prefix extends by repeating a strongly connected round, and rounds after t do not affect round-t vistas
--   - encoding: vistas up to isomorphism, given as explicit binary tables → well-formed VistaTable decoded to the published History value; reason: equal History values are exactly isomorphic vistas; malformed tables get the empty spectrum as in the source
--   - encoding: with polynomial bit length in s → ∃ C k before all inputs with Nat.size (K + ℓ + 2) ≤ C (1 + s)^k for well-formed inputs with ℓ ≥ 1; reason: uniform reading of 'polynomial'; Nat.size is the binary length
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 24 (PDF p. 26), Lemma 9

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Vistas

set_option autoImplicit false

open AnonymousDirectedCounting.Exact

namespace AnonymousDirectedCounting.Exact.Supplement

/-- Lemma 9, printed p. 24 (PDF p. 26). If the explicit vista `T` with leader count `ell` has two
different compatible orders, it has two different compatible orders at most `K + ℓ + 2`, where
`K = (1 + νM)^t`; and the bit length of `K + ℓ + 2` is bounded by a polynomial in the input length
`s`, with constants chosen before every input. -/
theorem two_small_orders :
    (∀ (T : VistaTable) (ell : ℕ),
      (∃ N₁ ∈ tableSpec ell T, ∃ N₂ ∈ tableSpec ell T, N₁ ≠ N₂) →
        ∃ N₁ ∈ tableSpec ell T, ∃ N₂ ∈ tableSpec ell T, N₁ ≠ N₂ ∧
          N₁ ≤ smallOrderBound ell T ∧ N₂ ≤ smallOrderBound ell T) ∧
    ∃ C k : ℕ, ∀ (T : VistaTable) (ell : ℕ), T.WellFormed → 0 < ell →
      Nat.size (smallOrderBound ell T) ≤ C * (1 + (encodeVistaInput T ell).length) ^ k := by sorry

end AnonymousDirectedCounting.Exact.Supplement
