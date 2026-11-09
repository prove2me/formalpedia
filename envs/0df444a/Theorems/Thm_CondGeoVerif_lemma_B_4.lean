-- Prove2me | Theorems.Thm_CondGeoVerif_lemma_B_4
-- name    : CondGeoVerif.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:38:50.386231+00:00
-- url     : https://prove2.me/theorems/b91196e7-62bb-4551-8098-049ecaa58225
-- title:
--   Lemma B.4 — $\mathbb E\exp\{t\|V^\top W\|_F^2\}\le(1-2tk^2/D)^{-1/2}$
-- statement:
--   Let $1\le k\le D$ and let $V,W$ be independent uniform elements of the Stiefel manifold of orthonormal $k$-frames in $\mathbb R^D$. For $0\le t<D/(2k^2)$,
--   $$\mathbb E\exp\{t\|V^\top W\|_F^2\}\le(1-2tk^2/D)^{-1/2}.$$
--   The bound holds also for $k=1$. It controls the overlap of two random hidden frames.
--
--   Differences from the source:
--   - encoding: independent uniform elements of the Stiefel manifold → a rotation-invariant probability measure ν carried by the Stiefel set, and the product ν ⊗ ν; reason: rotation invariance characterizes the uniform law
--   - encoding: the expectation of a positive random variable → a lower Lebesgue integral in [0, ∞]; reason: equal for nonnegative integrands; no integrability is presupposed
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Lemma B.4, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_CondGeoVerif_IsRotInvStiefelLaw

set_option autoImplicit false

open MeasureTheory
open scoped Matrix

namespace CondGeoVerif

/-- **Lemma B.4 (Haar-frame overlap moments)** (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, §B.4, p.26 = PDF p.29). Let `V, W` be
independent uniform elements of the Stiefel manifold of orthonormal `k`-frames in `ℝᴰ`. For
`0 ≤ t < D/(2k²)`, `E exp{t‖VᵀW‖_F²} ≤ (1 − 2tk²/D)^{−1/2}`. The proof is valid for `k = 1`.

**Formalization Note** The uniform law is any rotation-invariant probability measure carried by
the Stiefel set (`IsRotInvStiefelLaw`), which is the Haar law; independence is the product
`ν ⊗ ν`. The expectation is a lower Lebesgue integral of the nonnegative integrand, so no
integrability is presupposed. -/
theorem lemma_B_4 {D k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ D)
    (ν : ProbabilityMeasure (Matrix (Fin D) (Fin k) ℝ))
    (hν : IsRotInvStiefelLaw (ν : Measure (Matrix (Fin D) (Fin k) ℝ)))
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < D / (2 * k ^ 2)) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (t * frob (p.1ᵀ * p.2) ^ 2))
        ∂((ν : Measure (Matrix (Fin D) (Fin k) ℝ)).prod (ν : Measure (Matrix (Fin D) (Fin k) ℝ)))
      ≤ ENNReal.ofReal ((1 - 2 * t * k ^ 2 / D) ^ (-(1 / 2 : ℝ))) := by sorry

end CondGeoVerif
