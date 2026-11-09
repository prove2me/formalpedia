-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_24
-- name    : DetSupportRank.DeterminantSupport.lemma_5_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:43.759692+00:00
-- url     : https://prove2.me/theorems/2ac52ba8-2f68-4077-8456-a0be2ff9ec5b
-- title:
--   Lemma 5.24 — Both grading and map clauses under specialization
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ be graded, let $M$ be a graded $S$-module, and let $c\in F^m$ agree with the grading. Then the image pieces form a direct grading of the actual specialized vector space and
--   $$M(c)_u=\operatorname{span}_F\{m(c):m\in M_u\}.$$
--   Moreover, for every other graded module $N$ and every degree-preserving $S$-linear map $\psi:M\to N$, the actual induced map satisfies
--   $$\psi(c)(M(c)_u)\subseteq N(c)_u\qquad\text{for every }u.$$
--   There is no finite-generation, positivity, flatness, or specialized-exactness assumption in this statement.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: extension of scalars along evaluation S → F → quotient of the underlying F-vector space by the span of s m − s(c)m; reason: this is the same extension of scalars and includes every evaluated relation; image subspaces equal their F-spans
--   - generalization: M an S-module with finitely many homogeneous generators b_1,…,b_k (Definition 5.23, p.24) → an arbitrary graded S-module with integer-weighted S, no finite generation; reason: M(c) = M ⊗_S F is defined for every module and the grading argument uses only that the kernel of evaluation is a homogeneous ideal under agreement; finitely generated modules are special cases
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.24, p. 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Specialization

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 5.24, p.24. -/
theorem lemma_5_24 {K : Type*} [Field K] {m d : ℕ}
    (p : Fin m → Fin d → ℤ) (M : GradedModuleData K (Fin m) (Fin d))
    (hg : IsGraded p M) (c : Fin m → K) (hc : AgreesWithGrading p c) :
    IsDirectGrading (specializedPiece M c) ∧
    (∀ u, specializedPiece M c u = Submodule.span K
      {x | ∃ y ∈ M.piece u, specializationMap M c y = x}) ∧
    (∀ (N : GradedModuleData K (Fin m) (Fin d)), IsGraded p N →
      ∀ φ : M.Carrier →ₗ[MvPolynomial (Fin m) K] N.Carrier,
      PreservesDegrees M N φ → ∀ u, ∀ x ∈ specializedPiece M c u,
      specializeLinearMap M N c φ x ∈ specializedPiece N c u) := by sorry

end DetSupportRank.DeterminantSupport
