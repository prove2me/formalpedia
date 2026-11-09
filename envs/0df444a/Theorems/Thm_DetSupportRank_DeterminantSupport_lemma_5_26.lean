-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_26
-- name    : DetSupportRank.DeterminantSupport.lemma_5_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:58.240997+00:00
-- url     : https://prove2.me/theorems/2d6e66df-df0e-4730-8693-2f0fe6f70f45
-- title:
--   Lemma 5.26 — Exact specialization away from an annihilator
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$, let $B$ be an $S$-module, let $F_\bullet\to B$ be any free resolution, and assume $fB=0$. For every $c\in F^m$ with $f(c)\ne0$,
--   $$B(c)=0,\qquad F_\bullet(c)\longrightarrow B(c)\text{ is exact}.$$
--   All modules and maps are specialized by their actual induced evaluation maps. The resolution may be infinite and its free terms may have arbitrary rank. Its exactness before specialization is an input; exactness after specialization is the conclusion.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: extension of scalars along evaluation S → F → quotient of the underlying F-vector space by the span of s m − s(c)m; reason: this is the same extension of scalars and includes every evaluated relation; image subspaces equal their F-spans
--   - encoding: ungraded free resolutions in this lemma → module records with arbitrary candidate piece data and no grading predicate imposed; reason: the piece data impose no restriction and are unused; this quantifies over every ungraded free resolution
--   - generalization: B the finitely generated bigraded module of §5.7 and the specialized resolution 0 ⟶ F_ℓ(c) ⟶ ⋯ ⟶ F_0(c) ⟶ 0 is exact (pp.24–25) → B an arbitrary S-module; the conclusion is exactness of the augmented specialized complex ⋯ ⟶ F_1(c) ⟶ F_0(c) ⟶ B(c) ⟶ 0 together with B(c) = 0; reason: B(c) = 0 and exactness at F_0(c) give the source's exact sequence (surjectivity of F_1(c) ⟶ F_0(c)); the proof sketch on p.25 uses neither finite generation nor grading of B and derives B(c) = 0 from f(c) ≠ 0
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.26, p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Regrading

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 5.26, p.25. -/
theorem lemma_5_26 {K : Type*} [Field K] {m d : ℕ}
    (B : GradedModuleData K (Fin m) (Fin d)) (R : FreeResolutionData B)
    (f : MvPolynomial (Fin m) K) (hf : Annihilates f B)
    (c : Fin m → K) (hc : MvPolynomial.eval c f ≠ 0) :
    ExactSpecialization R c := by sorry

end DetSupportRank.DeterminantSupport
