-- Prove2me | Theorems.Thm_CosDensity_lemma_8_3
-- name    : CosDensity.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:27.973035+00:00
-- url     : https://prove2.me/theorems/4ae20be0-7ac5-45ab-8597-0ac7515edf4a
-- title:
--   Lemma 8.3 — finite-difference identity
-- statement:
--   Let $c_j=(-1)^{p-j}\binom pj$, $t_j=t_0+jh$ with $t_0=1/20$ and $h=2/(5p)$, for a fixed integer $p>2$. For all real $B,Z$ and every integer $0\le r\le p$,
--
--   $$\sum_{j=0}^p c_j\,(B+t_jZ)^r=\begin{cases}0,&0\le r<p,\\ p!\,h^p Z^p,&r=p.\end{cases}$$
--
--   This is the finite-difference identity that makes the two gadgets differ only in their $p$-th order response.
--
--   Differences from the source: none.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.3, Lemma 8.3, p.31 (pdf_page 32)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Lemma 8.3** (finite-difference identity). Q. Zhang, *Frequency Moments Beyond Equality:
Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.3,
Lemma 8.3, p.31 (pdf_page 32).

With `c_j = (−1)^{p−j} C(p, j)`, `t_j = t₀ + j h`, `t₀ = 1/20`, `h = 2/(5p)` (§8.3): for every
`B, Z ∈ ℝ` and every integer `0 ≤ r ≤ p`, `Σ_{j=0}^p c_j (B + t_j Z)^r` is `0` if `r < p` and
`p! h^p Z^p` if `r = p`.

**Formalization Note.** `p > 2` is §8.1's standing assumption. -/
theorem lemma_8_3 (p : ℕ) (hp : 2 < p) (B Z : ℝ) :
    (∀ r : ℕ, r < p →
      ∑ j ∈ Finset.range (p + 1), coef p j * (B + level p j * Z) ^ r = 0) ∧
    ∑ j ∈ Finset.range (p + 1), coef p j * (B + level p j * Z) ^ p =
      (p.factorial : ℝ) * hstep p ^ p * Z ^ p := by sorry

end CosDensity
