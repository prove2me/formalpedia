-- Prove2me | Theorems.Thm_CharPSComp_eq_2
-- name    : CharPSComp.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:44.459866+00:00
-- url     : https://prove2.me/theorems/5058956d-9f7d-4cf7-b81e-b8f750e57873
-- title:
--   (2) — a level merge as a polynomial matrix product: $J_{w,t}=\sum_jx^jC^{(w)}_{j,t}(x^k)$, $C=AH\bmod z^v$
-- statement:
--   In the setting of (1), suppose moreover $u=N/w=kv$. Let $G_r(x)\triangleq(\gamma_w(x))^r\bmod x^u$, let $A(z)$ be the $k\times k$ matrix with $A_{j,r}(z)\triangleq\sum_{i<v}([x^{ki+j}]G_r)z^i$, let $H(z)$ be the $k\times w$ matrix of child answers $H_{r,t}=J_{wk,t+wr}$, and put $C(z)\triangleq A(z)H(z)\bmod z^v$. Then for every $0\le t<w$
--   $$J_{w,t}(x)=\sum_{j=0}^{k-1}x^j\,C_{j,t}(x^k),$$
--   an equality of polynomials.
--
--   This turns a whole level of the recursion into one polynomial matrix product with a shared left matrix, which Sections 3.3–3.4 then compute by blocking and evaluation.
--
--   **Formalization Note** The matrices are index functions; `mergeOut` is $\sum_jx^jC_{j,t}(x^k)$ with $C_{j,t}=\big(\sum_rA_{j,r}H_{r,t}\big)\bmod z^v$.
--
--   Differences from the source:
--   - encoding: polynomial matrices $A^{(w)},H^{(w)},C^{(w)}$ → index functions `leftMat`, child answers, `mergeMat`; reason: same entries; no matrix type needed
--   - encoding: $w,k$ powers of $p$ with $kwv=N$ → $w=p^i$, $k=p^j$, $N/p^i=p^jv$; reason: the same objects with explicit exponents
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.2, display (2), p.7 (PDF p.8)

import Mathlib
import Definitions.Def_CharPSComp_J

open Polynomial

namespace CharPSComp

/-- Display (2) of Zhu, *Faster Power Series Composition in Fixed Positive Characteristic*, STOC
2027 submission (manuscript sha256 e63e0527…), §3.2, p.7 (PDF p.8).

In characteristic `p`, let `N = p^{⌈log_p n⌉}`, `w = pⁱ`, `k = pʲ` with `wk ∣ N` and
`u = N/w = kv`. Let `G_r(x) ≜ (γ_w(x))^r mod xᵘ`, let `A(z)` be the `k × k` matrix with
`A_{j,r}(z) ≜ Σ_{i<v} ([x^{ki+j}]G_r) zⁱ`, and let `H(z)` be the `k × w` matrix of child answers
`H_{r,t} = J_{wk,t+wr}`. Then, with `C(z) ≜ A(z)H(z) mod zᵛ`, for every `0 ≤ t < w`
`J_{w,t}(x) = Σ_{j=0}^{k−1} xʲ C_{j,t}(xᵏ)` (an equality of polynomials).

**Formalization Note** `mergeOut k v w G Hc t` is `Σ_j xʲ C_{j,t}(xᵏ)` with `C_{j,t}` the
truncated row–column product `Σ_r A_{j,r} H_{r,t} mod zᵛ` (`Def_CharPSComp_J`). -/
theorem eq_2 {R : Type*} [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (f g : R[X]) (hf : f.degree < m) (hg : g.degree < n)
    (i j v : ℕ) (hwk : p ^ i * p ^ j ∣ Npow p n) (hu : Npow p n / p ^ i = p ^ j * v)
    (t : ℕ) (ht : t < p ^ i) :
    J (Npow p n) m (p ^ i) t f g
      = mergeOut (p ^ j) v (p ^ i)
          (fun r => trunc (Npow p n / p ^ i) ((gamma (Npow p n) (p ^ i) g) ^ r))
          (fun c => J (Npow p n) m (p ^ i * p ^ j) c f g) t := by sorry

end CharPSComp
