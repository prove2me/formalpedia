-- Prove2me | Theorems.Thm_F3SubsetSum_theorem_4_19
-- name    : F3SubsetSum.theorem_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:51.206832+00:00
-- url     : https://prove2.me/theorems/c538d304-97ee-41e0-b6ba-6db82dabb900
-- title:
--   Theorem 4.19 — multiset shadow bound $|\partial\mathcal A|\ge|\mathcal A|^{1-1/r}$
-- statement:
--   Let $r\ge2$ and let $\mathcal A$ be a family of degree-$r$ monomials in $x_1,\dots,x_n$ (exponents unrestricted). Then
--
--   $$|\partial\mathcal A|\ge|\mathcal A|^{1-1/r}.$$
--
--   This is a consequence of the multiset analogue of Lovász's form of the Kruskal–Katona theorem [BBCH03], and it is the combinatorial input of Theorem 4.20.
--
--   Differences from the source: none.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 4.19, p.28

import Mathlib
import Definitions.Def_F3SubsetSum_MonomialShadow

namespace F3SubsetSum

/-- **Theorem 4.19** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 4.19,
p.28): "Let 𝒜 be a family of degree-r monomials where r ≥ 2. Then |∂𝒜| ≥ |𝒜|^{1−1/r}."

Monomials in `x_1, …, x_n` are exponent vectors (multisets over `[n]`, exponents unrestricted);
`∂` is the shadow of p.27. The family may be empty.

**Formalization Note** The power is a real power. -/
theorem theorem_4_19 (n r : ℕ) (hr : 2 ≤ r) (𝒜 : Finset (Fin n →₀ ℕ))
    (h𝒜 : ∀ α ∈ 𝒜, monoDeg α = r) :
    (𝒜.card : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ (shadow 𝒜).card := by sorry

end F3SubsetSum
