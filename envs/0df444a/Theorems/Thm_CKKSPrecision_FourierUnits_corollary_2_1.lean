-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_corollary_2_1
-- name    : CKKSPrecision.FourierUnits.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:47:57.066833+00:00
-- url     : https://prove2.me/theorems/9983e097-beaf-4c71-8f8e-56e73e9eb68a
-- title:
--   Corollary 2.1 — an explicit real basis of the zero-sum hyperplane
-- statement:
--   Let $r\ge2$ be any power of two, $m=4r$, and use the cyclic embedding order $\sigma_j(\zeta)=\zeta^{5^j}$. Let $H=\{t\in\mathbb R^r:\sum_jt_j=0\}$. Then
--   $$
--   \bigl(\operatorname{Log}(c_{5^h})\bigr)_{1\le h<r}
--   \text{ is linearly independent over }\mathbb R,
--   \qquad
--   \operatorname{span}_{\mathbb R}\{\operatorname{Log}(c_{5^h}):1\le h<r\}=H.
--   $$
--   Both assertions are part of the basis conclusion. The family uses $5^h$ inside the subscript of $c$, and supplies the full zero-sum target space needed for allocation.
--
--   Differences from the source:
--   - encoding: $K=\mathbb Q(\zeta)$ with the specified primitive complex root → Mathlib splitting field with the distinguished root sent to $\exp(2\pi i/m)$ by a fixed embedding; reason: an isomorphic model of the same field and root, with no additional hypothesis
--   - encoding: a basis indexed by $1\le h<r$ → linear independence of a family indexed by `Fin (r-1)` with exponent $5^{h+1}$, and equality of its span with $H$; reason: the shifted finite index gives exactly the source family, and independence together with this span equality is precisely the basis assertion
--   - encoding: a power-of-two integer dimension $r\ge2$ and real vectors in $\mathbb R^r$ with the infinity norm → a positive natural dimension with $r\ge2$, $r=2^q$ for some natural $q$, and functions `Fin r` to the reals with their supremum norm; reason: these encode exactly the same dimensions, coordinates and norm, without restricting target values
--   - encoding: Log with one arbitrarily chosen embedding from each conjugate pair (Section 2.3) → Log in the slot order $\sigma_j(\zeta)=\zeta^{5^j}$, $0\le j<r$, of Section 4.2; reason: the powers $5^j$ represent every conjugate pair exactly once; another selection permutes coordinates and replaces embeddings by conjugates of equal modulus, which preserves both independence and the span $H$
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, A New Approach to Reducing Modulus Requirements in Homomorphic Computation: Precision Allocation in CKKS, STOC 2027 submission #148 (October 2026), p. 5, Corollary 2.1 (PDF p. 7)

import Definitions.Def_CKKSPrecision_FourierUnits_fourier_construction

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits

theorem corollary_2_1 (r : ℕ+) (hr : 2 ≤ (r : ℕ))
    (hp : ∃ q : ℕ, (r : ℕ) = 2 ^ q) :
    LinearIndependent ℝ (basisVectors r) ∧
      Submodule.span ℝ (Set.range (basisVectors r)) = H (Fin (r : ℕ)) := by sorry

end CKKSPrecision.FourierUnits
