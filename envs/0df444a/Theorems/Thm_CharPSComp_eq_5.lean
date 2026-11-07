-- Prove2me | Theorems.Thm_CharPSComp_eq_5
-- name    : CharPSComp.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:45.794771+00:00
-- url     : https://prove2.me/theorems/6244de92-c01a-40be-8468-8fd945463d2b
-- title:
--   (5) — recovering $AH\bmod z^v$ from the block product: $C=\big(\sum_iz^{si}D_i(z)\big)\bmod z^v$ (any monic $h$, any shapes)
-- statement:
--   Let $R$ be a commutative ring, $h\in R[z]$ monic of degree $d$, $s\ge1$ with $2s-2<d$, $v\ge1$, $\tau=\lceil v/s\rceil$, and let $A$ ($a\times b$) and $H$ ($b\times c$) be matrices over $R[z]$ whose entries have degree $<v$. Encode each entry by blocks of width $s$ as $\widehat P(y)=\sum_{i<\tau}P_i(\bar z)y^i\in E[y]$, $E=R[z]/(h)$, let $D(y)\triangleq\widehat A(y)\widehat H(y)=\sum_{i=0}^{2\tau-2}D_i(\bar z)y^i$ and $D_i(z)\triangleq\mathrm{rep}_h(D_i(\bar z))$. Then entrywise
--   $$A(z)H(z)\bmod z^v=\Big(\sum_{i=0}^{2\tau-2}z^{si}D_i(z)\Big)\bmod z^v .$$
--
--   Because each block product has degree at most $2s-2<d$, reduction modulo $h$ loses nothing, so the product over $E[y]$ determines the product over $R[z]$.
--
--   Differences from the source:
--   - generalization: $h\in\mathbb F_p[z]$ irreducible of degree $d$ carried into $R$ of characteristic $p$, $A$ of shape $k\times k$ and $H$ of shape $k\times w$ → any commutative $R$, any monic $h\in R[z]$ of degree $d$ with $2s-2<d$, any shapes $a\times b$, $b\times c$; reason: the identity uses only monicity and the degree bound; the paper's case is an instance
--   - encoding: $2s-2<d$ → `2 * s < d + 2` with $s\ge1$; reason: the same inequality over $\mathbb N$
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.4, display (5), p.10 (PDF p.11)

import Mathlib
import Definitions.Def_CharPSComp_rep

open Polynomial

namespace CharPSComp

/-- Display (5) of Zhu, *Faster Power Series Composition in Fixed Positive Characteristic*, STOC
2027 submission (manuscript sha256 e63e0527…), §3.4, p.10 (PDF p.11).

Write every entry `P ∈ R[z]_{<v}` of the matrices `A` and `H` in blocks of width `s`,
`P = Σ_{i<τ} z^{si} P_i`, `τ ≜ ⌈v/s⌉`, encode `P̂(y) ≜ Σ_{i<τ} P_i(z̄) yⁱ ∈ E[y]` with
`E = R[z]/(h)`, and let `D(y) ≜ Â(y)Ĥ(y) = Σ_{i=0}^{2τ−2} D_i(z̄) yⁱ` and
`D_i(z) ≜ rep_h(D_i(z̄))`. Since `2s − 2 < d`,
`C(z) = A(z)H(z) mod zᵛ = (Σ_{i=0}^{2τ−2} z^{si} D_i(z)) mod zᵛ`.

**Formalization Note** Stated for any commutative ring `R`, any monic `h ∈ R[z]` of degree `d`, any
`s ≥ 1` with `2s − 2 < d` (written `2s < d + 2`), any `v ≥ 1`, and matrices of any shapes
`a × b` and `b × c` (entries indexed by natural numbers below the dimensions). The paper's case is
`h` the irreducible modulus over `F_p` carried into `R`, `A` of shape `k × k` and `H` of shape
`k × w`. -/
theorem eq_5 {R : Type*} [CommRing R] (h : R[X]) (hmonic : h.Monic) (d s v : ℕ)
    (hd : h.natDegree = d) (hs : 1 ≤ s) (hsd : 2 * s < d + 2) (hv : 1 ≤ v)
    (a b c : ℕ) (A H : ℕ → ℕ → R[X])
    (hA : ∀ j < a, ∀ r < b, (A j r).degree < v) (hH : ∀ r < b, ∀ t < c, (H r t).degree < v)
    (j t : ℕ) (hj : j < a) (ht : t < c) :
    trunc v (∑ r ∈ Finset.range b, A j r * H r t)
      = trunc v (∑ i ∈ Finset.range (2 * ((v + s - 1) / s) - 1),
          X ^ (s * i) * rep h ((∑ r ∈ Finset.range b,
            blockEncode h s ((v + s - 1) / s) (A j r)
              * blockEncode h s ((v + s - 1) / s) (H r t)).coeff i)) := by sorry

end CharPSComp
