-- Prove2me | Theorems.Thm_CosDensity_eq_37_38
-- name    : CosDensity.eq_37_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:27.159347+00:00
-- url     : https://prove2.me/theorems/2e4498e3-1b3b-4621-9858-af6441f4c84d
-- title:
--   (37)–(38) — the moment in the two cases of the queried bit
-- statement:
--   Fix an integer $p>2$, unit codewords with nonnegative coordinates, a coloring, $z$, $q$ and $\nu$, and let $Z_i$ be the code responses of $P(z,q)$.
--
--   1. If $\sum_{i\ne q}Z_i^p\le\nu Q^p$ (the conclusion of Lemma 8.7) and $z_q=0$, then
--   $$M_p(P(z,q))\le V_0(q)+\kappa_p\nu Q^p.\qquad(37)$$
--   2. If $z_q=1$, then
--   $$M_p(P(z,q))\ge V_0(q)+\kappa_pQ^p.\qquad(38)$$
--
--   The two bounds separate the cases of the queried bit.
--
--   Differences from the source:
--   - generalization: ν = 1/10 in Lemma 8.7, the §8 parameters, a balanced coloring → any ν, any N and m, any coloring, with the conclusion of Lemma 8.7 as the hypothesis of (37); reason: the paper's case is ν = 1/10 with Lemma 8.7's parameters; the derivation uses only Lemma 8.7's conclusion
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.7, (37)–(38), p.35 (pdf_page 36)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **(37)–(38)**: the two cases of the queried bit. Q. Zhang, *Frequency Moments Beyond
Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…),
§8.7, (37) and (38), p.35 (pdf_page 36).

If `Σ_{i≠q} Z_i^p ≤ ν Q^p` (the conclusion of Lemma 8.7) and `z_q = 0`, then
`M_p(P(z, q)) ≤ V₀(q) + κ_p ν Q^p` (37); if `z_q = 1`, then `M_p(P(z, q)) ≥ V₀(q) + κ_p Q^p` (38).

**Formalization Note.** The paper takes `ν = 1/10`; here `ν` is arbitrary. `Z_i` is the code
response of the vector sum of `P(z, q)`. -/
theorem eq_37_38 {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (ha : IsUnitNonnegCode a) (z : Fin N → Bool) (q : Fin N) (ν : ℝ) :
    (∑ i ∈ Finset.univ.erase q, codeResp a i (hardStream p a χ z q).sum ^ p ≤
        ν * queryAmp p m ^ p →
      z q = false →
      moment p (hardStream p a χ z q) ≤ baseline p a χ q + kappa p * ν * queryAmp p m ^ p) ∧
    (z q = true →
      baseline p a χ q + kappa p * queryAmp p m ^ p ≤ moment p (hardStream p a χ z q)) := by sorry

end CosDensity
