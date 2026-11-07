-- Prove2me | Theorems.Thm_CharPSComp_eq_9
-- name    : CharPSComp.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:52.817168+00:00
-- url     : https://prove2.me/theorems/73b80902-fdfe-44b5-8d66-e7fd7ed05a4d
-- title:
--   (9) — the Frobenius step for the lifted inner powers: $(h_j(x))^q\equiv h_{j+b}(x^q)\pmod{x^{u_j}}$
-- statement:
--   Let $R$ be a nonzero commutative ring of characteristic $p^e$, $e\ge1$, $\eta=p^{e-1}$, $m,n\ge1$, $g\in R[x]$ with $\deg g<n$, $N=p^{\lceil\log_pn\rceil}$, $a=\lceil\log_p\sigma\rceil$ with $\sigma=\min(m,n)$, $u_j\triangleq N/p^j$ and $h_j(x)\triangleq(\gamma_{p^j}(x))^\eta\bmod x^{u_j}$. For $j+b\le a$ and $q=p^b$,
--   $$(h_j(x))^q\equiv h_{j+b}(x^q)\pmod{x^{u_j}} .$$
--   The case $b=1$ is the page's one-digit version $(h_j(x))^p\equiv h_{j+1}(x^p)\pmod{x^{u_j}}$ for $j<a$.
--
--   This is the prime-power analogue of the first clause of Lemma 1, used at every grouped and single-digit step of Algorithm 3.
--
--   **Formalization Note** The congruence is equality of truncations to precision $u_j$; $h(x^q)$ is `expand R q h`.
--
--   Differences from the source:
--   - encoding: $F\equiv G\pmod{x^{u_j}}$ → `trunc (N / p ^ j) F = trunc (N / p ^ j) G`; reason: equal truncations are the same congruence
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.6.1, display (9) and the sentence after it, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_CharPSComp_J

open Polynomial

namespace CharPSComp

/-- Display (9) of Zhu, *Faster Power Series Composition in Fixed Positive Characteristic*, STOC
2027 submission (manuscript sha256 e63e0527…), §3.6.1, p.15 (PDF p.16).

Let `R` have characteristic `pᵉ`, `e ≥ 1`, `η = p^{e−1}`, `N = p^{⌈log_p n⌉}`, `K = p^a` with
`a = ⌈log_p σ⌉`, `u_j ≜ N/pʲ` and `h_j(x) ≜ (γ_{pʲ}(x))^η mod x^{u_j}`. For `j + b ≤ a` and
`q = p^b`,
`(h_j(x))^q ≡ h_{j+b}(x^q) (mod x^{u_j})`.
The case `b = 1` is the page's one-digit version `(h_j(x))^p ≡ h_{j+1}(x^p) (mod x^{u_j})` for
`j < a`.

**Formalization Note** The congruence is equality of truncations `trunc (N / pʲ)`; `h(x^q)` is
`expand R q h`. The standing data (`m, n ≥ 1`, `deg g < n`) are hypotheses. -/
theorem eq_9 {R : Type*} [CommRing R] [Nontrivial R] (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    [CharP R (p ^ e)] (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (g : R[X]) (hg : g.degree < n)
    (j b : ℕ) (hjb : j + b ≤ Nat.clog p (min m n)) :
    trunc (Npow p n / p ^ j) ((hpow (Npow p n) p (p ^ (e - 1)) j g) ^ (p ^ b))
      = trunc (Npow p n / p ^ j)
          (expand R (p ^ b) (hpow (Npow p n) p (p ^ (e - 1)) (j + b) g)) := by sorry

end CharPSComp
