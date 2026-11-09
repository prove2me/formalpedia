-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_25
-- name    : DetSupportRank.DeterminantSupport.lemma_5_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:21.794315+00:00
-- url     : https://prove2.me/theorems/edee6df9-daf2-4dd1-8215-208d226b0916
-- title:
--   Lemma 5.25 — Free K-polynomial after regrading and specialization
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ have nonnegative variable bidegrees, and let a finite free bigraded module have basis shifts $(s_i,t_i)\in\mathbb Z^d\times\mathbb Z^d$. For arbitrary integers $a,b$, regrade by $a\deg_1+b\deg_2$ and specialize at any agreeing point $c$. Then
--   $$K_{F'(c)}^F(t)=K_F^S(t^a,t^b).$$
--   The left side is the finite Laurent Hilbert polynomial of the specialized vector space. No finite-dimensionality of homogeneous pieces before specialization is required, and negative regraded shifts remain representable.
--
--   Differences from the source:
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - encoding: extension of scalars along evaluation S → F → quotient of the underlying F-vector space by the span of s m − s(c)m; reason: this is the same extension of scalars and includes every evaluated relation; image subspaces equal their F-spans
--   - generalization: nonnegative basis bidegrees in the displayed free-module presentation on p.24 → arbitrary integer basis bidegrees; reason: regrading and specialization preserve the homogeneous basis with shifts a s_i+b t_i regardless of their signs; the nonnegative source case is included
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.25, p. 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Regrading
import Definitions.Def_DetSupportRank_DeterminantSupport_InitialModules

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 5.25, p.24. -/
theorem lemma_5_25 {K : Type*} [Field K] {m d k : ℕ}
    (p q : Fin m → Fin d → ℕ) (s t : Fin k → Fin d → ℤ)
    (a b : ℤ) (c : Fin m → K)
    (hc : AgreesWithGrading (fun j i => a * (p j i : ℤ) + b * (q j i : ℤ)) c) :
    vectorKPolynomial (specializedPiece
      (freeModuleData (K := K) (fun j i => a * (p j i : ℤ) + b * (q j i : ℤ))
        (fun j i => a * (s j i : ℤ) + b * (t j i : ℤ))) c) =
    regradeLaurent (combineDegrees a b)
      (kPolynomial (pairDegrees (fun j i => (p j i : ℤ)) (fun j i => (q j i : ℤ)))
        (freeModuleData (K := K)
          (pairDegrees (fun j i => (p j i : ℤ)) (fun j i => (q j i : ℤ)))
          (fun j => Sum.elim (fun i => (s j i : ℤ)) (fun i => (t j i : ℤ))))) := by sorry

end DetSupportRank.DeterminantSupport
