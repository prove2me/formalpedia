-- Prove2me | Theorems.Thm_BoundEntGauss_family_physical_iff
-- name    : BoundEntGauss.family_physical_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:59.342455+00:00
-- url     : https://prove2.me/theorems/4b442ea0-c1e4-4edb-8d98-adcf6544ff93
-- title:
--   Section IV, after Eq. (11) — $\gamma(a,b,c,e,f)+i\sigma\ge0$ iff $a<ce$
-- statement:
--   Let $a,b,c,e,f>0$ with $a\ne ce$, and let $\gamma=\gamma(a,b,c,e,f)$ be the family covariance. Then
--
--   $$
--   \gamma+i\sigma\ge0\iff a<ce .
--   $$
--
--   The paper states "$\gamma+i\sigma\ge0$ iff $a\le ce$, where equality is ruled out since this would be equivalent to $\det(\Omega)=0$". So the family (11) consists of covariance matrices of quantum states exactly on the region $a<ce$, which is the parameter region of the goal.
--
--   Differences from the source:
--   - encoding: "γ + iσ ≥ 0 iff a ≤ ce, where equality is ruled out" → hypothesis a ≠ c·e and conclusion ↔ a < c·e; reason: at a = ce the construction is undefined (det Ω = 0); away from it, a ≤ ce is a < ce
--   - encoding: γ defined by the construction γ = ΛΩ⁻¹ from Ω₁ of (11), with d = (bc+f)/a → the closed form wwGamma a b c e f, tied to the construction by the milestone family_construction; reason: an explicit matrix instead of an opaque inverse; same matrix
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, p. 4 (after Eq. (11))

import Mathlib
import Definitions.Def_BoundEntGauss_totalSigma
import Definitions.Def_BoundEntGauss_wwGamma

open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (covarianceBlockMatrix)

namespace BoundEntGauss

/-- **The family satisfies γ + iσ ≥ 0 exactly when a < ce.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, p. 4: "from the characteristic function of ⟨Ω_k, Λ_l + iσΩ_l⟩ we obtain that
γ + iσ ≥ 0 iff a ≤ ce, where equality is ruled out since this would be equivalent to
det(Ω) = 0."

For `a, b, c, e, f > 0` with `a ≠ c·e`, the matrix `γ = γ(a, b, c, e, f)` satisfies `γ + iσ ≥ 0`
if and only if `a < c·e`.

**Formalization Note.** "`a ≤ c·e`, where equality is ruled out" is `a < c·e`; the case `a = c·e`
is excluded by the hypothesis `a ≠ c·e`, where the construction (and the closed form) is
undefined. -/
theorem family_physical_iff (a b c e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hf : 0 < f) (hace : a ≠ c * e) :
    (complexify (covarianceBlockMatrix (wwGamma a b c e f)) +
        Complex.I • complexify (totalSigma 2 2)).PosSemidef ↔ a < c * e := by sorry

end BoundEntGauss
