-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_16
-- name    : DetSupportRank.DeterminantSupport.lemma_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:12.209324+00:00
-- url     : https://prove2.me/theorems/b0e455a5-283c-4fab-bf3d-0076ee416a4e
-- title:
--   Lemma 5.16 — K-polynomial of the actual cokernel
-- statement:
--   Over any field, let $n>0$ and $D$ have determinant support. Fix $a,b$, a homogeneous relation matrix $A$, and $k\ge0$ with $\det A\mid D^k$, and form $M=P^b/\operatorname{im}A$. Then
--   $$K_M^P(z)=q_{a,b}(z)=\sum_i(z^{b_i}-z^{a_i}).$$
--   The target and source shifts are both arbitrary nonnegative tuples, and the sign is target minus source. Polynomial equality is represented through its injective embedding in the Laurent ring.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: independent nonzero field coefficients cσ → a function from permutations to field units; reason: every nonzero field element determines a unique unit, so this parametrizes exactly the source family
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.16, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Cokernels

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 5.16, p.22. -/
theorem lemma_5_16 {K : Type*} [Field K] {n N : ℕ} (hn : 0 < n)
    (c : Equiv.Perm (Fin n) → Kˣ) (a b : Fin N → Fin n → ℕ)
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin n × Fin n) K))
    (k : ℕ) (hA : IsRelationWitness (determinantSupportPolynomial c) a b A k) :
    kPolynomial rowWeight (rowCokernel b A) = naturalToLaurent (relationTest a b) := by sorry

end DetSupportRank.DeterminantSupport
