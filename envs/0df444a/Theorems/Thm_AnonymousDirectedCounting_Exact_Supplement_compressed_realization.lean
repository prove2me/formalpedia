-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_Supplement_compressed_realization
-- name    : AnonymousDirectedCounting.Exact.Supplement.compressed_realization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:54:33.931205+00:00
-- url     : https://prove2.me/theorems/a2a47f54-39d8-4cf1-a433-176d82422cec
-- title:
--   Lemma 12 — compressed realization of the same order
-- statement:
--   Let $\mathcal V$ be an explicit vista with levels $L_0,\dots,L_t$ and leader count $\ell$, with input length $s$. If $\mathcal V$ has a realization of order $N$, it has a realization of the same order $N$ and the same leader count $\ell$ whose full history-tree levels $T_0,\dots,T_t$ satisfy
--   $$|T_r|\le\sum_{j=0}^r|L_j|+r+2\qquad(0\le r\le t).$$
--   Its anonymities, outdegrees and red multiplicities through level $t$ have $O(s+\log N)$ bits, and the description of its entire full prefix through level $t$ has length polynomial in $s+\log N$. Both the $O$-constant and the polynomial are fixed before every input.
--
--   The lemma supplies a polynomial-size certificate for every compatible order.
--
--   **Formalization Note** The conclusion includes an actual binary full-prefix certificate, all its finite-table checks, and its semantic identification with the new realization. The same universal constants bound its encoded length.
--
--   Differences from the source:
--   - encoding: a realization is a finite network prefix through round t, strongly connected in each round → a network strongly connected in every round (published Admissible); reason: a prefix extends by repeating a strongly connected round, and rounds after t do not affect round-t vistas
--   - encoding: vistas up to isomorphism, given as explicit binary tables → well-formed VistaTable decoded to the published History value; reason: equal History values are exactly isomorphic vistas; malformed tables get the empty spectrum as in the source
--   - encoding: O(s + log N) bits → ∃ C before all inputs with Nat.size ≤ C (1 + s + Nat.size N); reason: Nat.size N = ⌊log₂ N⌋ + 1; the constant is uniform
--   - encoding: the entire full-prefix description has length polynomial in s + log N → a FullPrefixCertificate valid for the input and representing the same network, with encode.length ≤ C (1 + s + Nat.size N)^k, as well as the dense numerical-size bound fullPrefixSize; reason: the certificate encoding includes node ids, parents, labels, anonymities and delimiters; dense and sparse table sizes are polynomially related
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 26 (PDF p. 28), Lemma 12

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Certificates

set_option autoImplicit false

open AnonymousDirectedCounting.Exact

namespace AnonymousDirectedCounting.Exact.Supplement

/-- Lemma 12, printed p. 26 (PDF p. 28). There are constants `C, k`, fixed before every input, such
that whenever the explicit vista `T` (with `t = depth` and levels `L_j`) has a realization of order
`N` with `ell` leaders, it has one of the same order and leader count whose full levels satisfy
`|T_r| ≤ ∑_{j ≤ r} |L_j| + r + 2` for `r ≤ t`, whose anonymities, outdegree labels and red
multiplicities through level `t` have at most `C (1 + s + log N)` bits, and whose full-prefix
description has length at most `C (1 + s + log N)^k`, where `s` is the input length. -/
theorem compressed_realization :
    ∃ C k : ℕ, ∀ (T : VistaTable) (ell N : ℕ), N ∈ tableSpec ell T →
      ∃ G : NetworkModel N, Admissible G ∧ G.leaders.card = ell ∧
        (∃ x : Fin N, history G T.depth x = T.decode) ∧
        (∀ r, r ≤ T.depth → (historyLevel G r).card ≤
          ∑ j ∈ Finset.range (r + 1), (vistaLevel T.depth T.decode j).card + r + 2) ∧
        (∀ r, r ≤ T.depth → ∀ v ∈ historyLevel G r, Nat.size (anonymity G r v) ≤
          C * (1 + (encodeVistaInput T ell).length + Nat.size N)) ∧
        (∀ r, r < T.depth → ∀ v ∈ historyLevel G (r + 1),
          Nat.size (outLabel v) ≤ C * (1 + (encodeVistaInput T ell).length + Nat.size N) ∧
          ∀ u ∈ historyLevel G r, Nat.size (redMult u v) ≤
            C * (1 + (encodeVistaInput T ell).length + Nat.size N)) ∧
        fullPrefixSize G T.depth ≤
          C * (1 + (encodeVistaInput T ell).length + Nat.size N) ^ k ∧
        ∃ cert : FullPrefixCertificate, cert.ValidFor T ell N ∧ cert.Represents G ∧
          cert.encode.length ≤ C * (1 + (encodeVistaInput T ell).length + Nat.size N) ^ k := by sorry

end AnonymousDirectedCounting.Exact.Supplement
