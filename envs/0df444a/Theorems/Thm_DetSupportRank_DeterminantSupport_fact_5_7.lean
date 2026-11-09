-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_fact_5_7
-- name    : DetSupportRank.DeterminantSupport.fact_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:28.281747+00:00
-- url     : https://prove2.me/theorems/90c8d6ae-964e-409e-b564-81ccd279426e
-- title:
--   Fact 5.7 — Both additivity statements for K-polynomials
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ have an integer multigrading. Every degree-preserving short exact sequence of finitely generated graded modules satisfies
--   $$0\to M''\to M'\to M\to0\quad\Longrightarrow\quad K_M^S=K_{M'}^S-K_{M''}^S.$$
--   For every finite degree-preserving exact sequence of finitely generated graded modules, the additional assertion is
--   $$0\to M_0\to\cdots\to M_\ell\to0\quad\Longrightarrow\quad\sum_{i=0}^{\ell}(-1)^iK_{M_i}^S=0.$$
--   Both clauses use actual linear maps and exactness. The resolution-defined version also covers the source's regraded application.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - generalization: positive nonnegative grading for the Hilbert-numerator statement, with resolution-defined extension on p.19 → arbitrary integer multigrading with resolution-defined K-polynomials; reason: Remark 5.10 identifies this with the Hilbert numerator on the original domain; the same Euler additivity applies without positivity
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Fact 5.7, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Regrading

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Fact 5.7, p.18. -/
theorem fact_5_7 {K : Type*} [Field K] {m d : ℕ}
    (p : Fin m → Fin d → ℤ) :
    (∀ (M₀ M₁ M₂ : GradedModuleData K (Fin m) (Fin d)),
      Module.Finite (MvPolynomial (Fin m) K) M₀.Carrier →
      Module.Finite (MvPolynomial (Fin m) K) M₁.Carrier →
      Module.Finite (MvPolynomial (Fin m) K) M₂.Carrier →
      IsGraded p M₀ → IsGraded p M₁ → IsGraded p M₂ →
      ∀ (φ : M₀.Carrier →ₗ[MvPolynomial (Fin m) K] M₁.Carrier)
        (ψ : M₁.Carrier →ₗ[MvPolynomial (Fin m) K] M₂.Carrier),
      PreservesDegrees M₀ M₁ φ → PreservesDegrees M₁ M₂ ψ →
      Function.Injective φ → Function.Surjective ψ → LinearMap.range φ = LinearMap.ker ψ →
      kPolynomial p M₂ = kPolynomial p M₁ - kPolynomial p M₀) ∧
    (∀ E : FiniteExactSequence (K := K) p,
      (∑ i ∈ Finset.range (E.length + 1),
        (-1 : ℤ) ^ i • kPolynomial p (E.term i)) = 0) := by sorry

end DetSupportRank.DeterminantSupport
