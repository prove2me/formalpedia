-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_19
-- name    : DetSupportRank.DeterminantSupport.lemma_5_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:30.46419+00:00
-- url     : https://prove2.me/theorems/13c6ccdd-b329-40ae-9866-9317418407c7
-- title:
--   Lemma 5.19 — The same initial cokernel is annihilated
-- statement:
--   Over any field, let $n>0$, $D$ have determinant support, and fix a witnessing matrix $A$ for $a\sim_D b$ together with $\det A\mid D^k$. For the same constructed initial quotient $M^\sharp=P^b/\operatorname{in}(\operatorname{im}A)$, with target basis column shifts zero,
--   $$D^kM^\sharp=0.$$
--   Annihilation of $M$ is not added as an assumption: the fixed witness data are the source data and Lemma 5.15 supplies that intermediate result.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: independent nonzero field coefficients cσ → a function from permutations to field units; reason: every nonzero field element determines a unique unit, so this parametrizes exactly the source family
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.19, p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Cokernels

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 5.19, p.23. -/
theorem lemma_5_19 {K : Type*} [Field K] {n N : ℕ} (hn : 0 < n)
    (c : Equiv.Perm (Fin n) → Kˣ) (a b : Fin N → Fin n → ℕ)
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin n × Fin n) K))
    (k : ℕ) (hA : IsRelationWitness (determinantSupportPolynomial c) a b A k) :
    Annihilates (determinantSupportPolynomial c ^ k) (bigradedCokernel b A) := by sorry

end DetSupportRank.DeterminantSupport
