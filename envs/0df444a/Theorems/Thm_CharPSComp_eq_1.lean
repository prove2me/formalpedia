-- Prove2me | Theorems.Thm_CharPSComp_eq_1
-- name    : CharPSComp.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:22.399446+00:00
-- url     : https://prove2.me/theorems/efcb3838-656a-441b-bfae-ec9927e9dc74
-- title:
--   (1) — the parent answer $J_{w,t}\equiv\sum_r(\gamma_w)^rH^{(w)}_{r,t}(x^k)\pmod{x^u}$
-- statement:
--   Let $R$ be a nonzero commutative ring of prime characteristic $p$, $m,n\ge1$, $f,g\in R[x]$ with $\deg f<m$, $\deg g<n$, $N=p^{\lceil\log_pn\rceil}$. Let $w=p^i$ and $k=p^j$ with $wk\mid N$, $u=N/w$, and $0\le t<w$. With the child answers $H^{(w)}_{r,t}(z)\triangleq J_{wk,t+wr}(z)$,
--   $$J_{w,t}(x)\equiv\sum_{r=0}^{k-1}(\gamma_w(x))^r\,H^{(w)}_{r,t}(x^k)\pmod{x^u}.$$
--
--   This is one step of the Frobenius recursion: the answer at a node is recovered from the answers of its $k$ children at the next width.
--
--   **Formalization Note** The congruence is equality of truncations to precision $u$; $H(x^k)$ is `expand R k H`.
--
--   Differences from the source:
--   - encoding: $F\equiv G\pmod{x^u}$ → `trunc u F = trunc u G`; reason: equal truncations are the same congruence
--   - encoding: $w,k$ powers of $p$ with $wk\mid N$ → $w=p^i$, $k=p^j$, $p^ip^j\mid N$; reason: the same objects with explicit exponents
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.1, display (1), p.7 (PDF p.8)

import Mathlib
import Definitions.Def_CharPSComp_J

open Polynomial

namespace CharPSComp

/-- Display (1) of Zhu, *Faster Power Series Composition in Fixed Positive Characteristic*, STOC
2027 submission (manuscript sha256 e63e0527…), §3.1, p.7 (PDF p.8).

In characteristic `p`, let `N = p^{⌈log_p n⌉}`, `w = pⁱ`, `k = pʲ` with `wk ∣ N`, `u = N/w`,
and `0 ≤ t < w`. With the child answers `H^{(w)}_{r,t}(z) ≜ J_{wk,t+wr}(z)`, the parent is recovered
by
`J_{w,t}(x) ≡ Σ_{r=0}^{k−1} (γ_w(x))^r H^{(w)}_{r,t}(xᵏ) (mod xᵘ)`.

**Formalization Note** The congruence is equality of truncations to precision `u = N/w`;
`H(xᵏ)` is `expand R k H`. The standing data of §3 (`m, n ≥ 1`, `deg f < m`, `deg g < n`) are
hypotheses. -/
theorem eq_1 {R : Type*} [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (f g : R[X]) (hf : f.degree < m) (hg : g.degree < n)
    (i j : ℕ) (hwk : p ^ i * p ^ j ∣ Npow p n) (t : ℕ) (ht : t < p ^ i) :
    trunc (Npow p n / p ^ i) (J (Npow p n) m (p ^ i) t f g)
      = trunc (Npow p n / p ^ i)
          (∑ r ∈ Finset.range (p ^ j), (gamma (Npow p n) (p ^ i) g) ^ r
            * expand R (p ^ j) (J (Npow p n) m (p ^ i * p ^ j) (t + p ^ i * r) f g)) := by sorry

end CharPSComp
