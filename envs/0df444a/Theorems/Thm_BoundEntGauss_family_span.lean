-- Prove2me | Theorems.Thm_BoundEntGauss_family_span
-- name    : BoundEntGauss.family_span
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:54.038005+00:00
-- url     : https://prove2.me/theorems/329e21e4-b1c3-4479-b325-566e3bc59b0a
-- title:
--   Section IV — the condition of Proposition 3 holds for $\gamma(a,b,c,e,f)$
-- statement:
--   Let $a,b,c,e,f>0$ with $a<ce$ and $\gamma=\gamma(a,b,c,e,f)$. Let $\mathcal N$ and $\tilde{\mathcal N}$ be the null spaces of $\gamma+i\sigma$ and $\gamma+i\tilde\sigma$ in $\mathbb C^8$. Then
--
--   $$
--   \Re\mathfrak e\,\mathcal N+\Re\mathfrak e\,\tilde{\mathcal N}=\mathbb R^8 .
--   $$
--
--   By Proposition 3, a ppt-covariance of the family is therefore minimally ppt. The paper says the condition "is satisfied by construction": the eight vectors obtained from $\Omega_1$ lie in $\mathcal N$, $\tilde{\mathcal N}$ or their complex conjugates and form a basis.
--
--   Differences from the source:
--   - reading: "the condition of Proposition 3 is satisfied by construction", printed for the example (9)–(10) → the span condition for every member γ(a,b,c,e,f) with a < ce; reason: the family (11) is built "in the same manner as above", and the paper asserts its members are bound entangled, which uses this condition; the example is the member (1,1,2,1,1)
--   - encoding: γ defined by the construction γ = ΛΩ⁻¹ from Ω₁ of (11), with d = (bc+f)/a → the closed form wwGamma a b c e f, tied to the construction by the milestone family_construction; reason: an explicit matrix instead of an opaque inverse; same matrix
--   - encoding: "ℜeN and ℜeÑ together span X" → realPartSpan N ⊔ realPartSpan Ñ = ⊤ in the lattice of real subspaces of ℝ⁸; reason: the supremum of two subspaces is their sum
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, p. 4 (after Eq. (10), extended to (11) by "in the same manner as above")

import Mathlib
import Definitions.Def_BoundEntGauss_totalSigma
import Definitions.Def_BoundEntGauss_sigmaTilde
import Definitions.Def_BoundEntGauss_nullSpace
import Definitions.Def_BoundEntGauss_realPartSpan
import Definitions.Def_BoundEntGauss_wwGamma

open QAlgorithms.Papers.Independent.Intakenext100.P68 (covarianceBlockMatrix)

namespace BoundEntGauss

/-- **The condition of Proposition 3 holds for the family.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, p. 4: "Then the condition of Proposition 3 is satisfied by construction" (said of
the example (9)–(10); the family (11) is built "in the same manner as above").

For `a, b, c, e, f > 0` with `a < c·e` and `γ = γ(a, b, c, e, f)`, the real parts `ℜe N` and
`ℜe Ñ` of the null spaces of `γ + iσ` and `γ + iσ̃` together span `ℝ⁸`.

**Formalization Note.** The printed sentence is about (9); its family version is the paper's "in
the same manner as above" before (11), cited at the same place. -/
theorem family_span (a b c e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hf : 0 < f) (hace : a < c * e) :
    realPartSpan (nullSpace (covarianceBlockMatrix (wwGamma a b c e f)) (totalSigma 2 2)) ⊔
      realPartSpan (nullSpace (covarianceBlockMatrix (wwGamma a b c e f)) (sigmaTilde 2 2)) = ⊤ := by sorry

end BoundEntGauss
