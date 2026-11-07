-- Prove2me | Theorems.Thm_CharPSComp_lemma_1
-- name    : CharPSComp.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:10.300017+00:00
-- url     : https://prove2.me/theorems/f008cdcf-d923-4c2a-916d-88102d4fa847
-- title:
--   Lemma 1 — Frobenius and truncation: $(\gamma_w(x))^k\equiv\gamma_{wk}(x^k)\pmod{x^u}$ and the $z^v$/$x^u$ congruence transfer
-- statement:
--   Let $R$ be a nonzero commutative ring of prime characteristic $p$, $n\ge1$, $g\in R[x]$ with $\deg g<n$, and $N=p^{\lceil\log_pn\rceil}$. Let $w=p^i$ divide $N$, let $k=p^j$, put $u=N/w$, and suppose $u=kv$ for a positive integer $v$. Then
--
--   1. $$(\gamma_w(x))^k\equiv\gamma_{wk}(x^k)\pmod{x^u};$$
--   2. for all $B,C\in R[z]$: $B\equiv C\pmod{z^v}$ if and only if $B(x^k)\equiv C(x^k)\pmod{x^u}$.
--
--   The first clause is what lets a level of the recursion pass from width $w$ to width $wk$ with the precision divided by $k$; the second moves congruences between the child and parent precisions.
--
--   **Formalization Note** "$\equiv\pmod{x^u}$" is equality of truncations to precision $u$; $B(x^k)$ is `expand R k B`.
--
--   Differences from the source:
--   - encoding: $F\equiv G\pmod{x^u}$ → `trunc u F = trunc u G`; reason: equal truncations are the same congruence
--   - encoding: $w$ a power of $p$ dividing $N$, $k$ a power of $p$ → $w=p^i$ with $p^i\mid N$, $k=p^j$; reason: the same objects with explicit exponents
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 1, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_CharPSComp_J

open Polynomial

namespace CharPSComp

/-- Lemma 1 (Frobenius and truncation) of Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), p.6 (PDF p.7).

In characteristic `p`, with `N = p^{⌈log_p n⌉}`, `w = pⁱ` dividing `N`, `k = pʲ`, `u = N/w` and
`u = kv` for a positive integer `v`:
1. `(γ_w(x))ᵏ ≡ γ_{wk}(xᵏ) (mod xᵘ)`;
2. for `B, C ∈ R[z]`, `B ≡ C (mod zᵛ)` if and only if `B(xᵏ) ≡ C(xᵏ) (mod xᵘ)`.

**Formalization Note** "`≡ (mod xᵘ)`" is equality of truncations `trunc u`; `B(xᵏ)` is
`expand R k B`. The standing data of §3 (a nonzero ring of prime characteristic `p`, `n ≥ 1`,
`deg g < n`) are hypotheses. -/
theorem lemma_1 {R : Type*} [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (n : ℕ) (hn : 1 ≤ n) (g : R[X]) (hg : g.degree < n)
    (i j v : ℕ) (hw : p ^ i ∣ Npow p n) (hu : Npow p n / p ^ i = p ^ j * v) (hv : 1 ≤ v) :
    trunc (Npow p n / p ^ i) ((gamma (Npow p n) (p ^ i) g) ^ (p ^ j))
        = trunc (Npow p n / p ^ i) (expand R (p ^ j) (gamma (Npow p n) (p ^ i * p ^ j) g)) ∧
      ∀ B C' : R[X], trunc v B = trunc v C' ↔
        trunc (Npow p n / p ^ i) (expand R (p ^ j) B)
          = trunc (Npow p n / p ^ i) (expand R (p ^ j) C') := by sorry

end CharPSComp
