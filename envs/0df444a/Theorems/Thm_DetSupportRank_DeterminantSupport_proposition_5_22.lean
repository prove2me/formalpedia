-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_proposition_5_22
-- name    : DetSupportRank.DeterminantSupport.proposition_5_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:26.993274+00:00
-- url     : https://prove2.me/theorems/90fcf9c4-278e-4d8b-a11a-3cb321c7fafc
-- title:
--   Proposition 5.22 — Regraded K-polynomial vanishes
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ have two nonnegative multigradings, and let $B$ be a finitely generated bigraded $S$-module. Let a polynomial $f$ be homogeneous in both gradings and satisfy $fB=0$. For any integers $a,b$, and any $c\in F^m$ which agrees with $a\deg_1+b\deg_2$ and satisfies $f(c)\ne0$,
--   $$K_B^S(t^a,t^b)=0$$
--   as an integer Laurent polynomial. Permuting coordinates of either grading is allowed by the arbitrary weight data. Specialized exactness and the displayed vanishing are not hypotheses.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - encoding: extension of scalars along evaluation S → F → quotient of the underlying F-vector space by the span of s m − s(c)m; reason: this is the same extension of scalars and includes every evaluated relation; image subspaces equal their F-spans
--   - generalization: nonnegative module bidegrees in the standing bigraded setting → integer module bidegrees over the same nonnegative ring weights; reason: the finite graded resolution and evaluation argument permits arbitrary integer basis shifts; every nonnegative source module is included
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 5.22, p. 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Regrading
import Definitions.Def_DetSupportRank_DeterminantSupport_InitialModules

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Proposition 5.22, p.24. -/
theorem proposition_5_22 {K : Type*} [Field K] {m d : ℕ}
    (p q : Fin m → Fin d → ℕ)
    (B : GradedModuleData K (Fin m) (Fin d ⊕ Fin d))
    (hB : IsGraded (pairDegrees (fun j i => (p j i : ℤ)) (fun j i => (q j i : ℤ))) B)
    (hfg : Module.Finite (MvPolynomial (Fin m) K) B.Carrier)
    (f : MvPolynomial (Fin m) K)
    (hhom : ∃ u v : Fin d → ℕ,
      Homogeneous (fun j i => (p j i : ℤ)) (fun i => (u i : ℤ)) f ∧
      Homogeneous (fun j i => (q j i : ℤ)) (fun i => (v i : ℤ)) f)
    (hf : Annihilates f B) (a b : ℤ) (c : Fin m → K)
    (hagree : AgreesWithGrading (fun j i => a * (p j i : ℤ) + b * (q j i : ℤ)) c)
    (hc : MvPolynomial.eval c f ≠ 0) :
    regradeLaurent (combineDegrees a b)
      (kPolynomial (pairDegrees (fun j i => (p j i : ℤ)) (fun j i => (q j i : ℤ))) B) = 0 := by sorry

end DetSupportRank.DeterminantSupport
