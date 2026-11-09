-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_17
-- name    : DetSupportRank.DeterminantSupport.lemma_5_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:13.119999+00:00
-- url     : https://prove2.me/theorems/8d117f25-d5c1-4fb8-8fec-202d84d8ed35
-- title:
--   Lemma 5.17 — Canonical row-column graded replacement
-- statement:
--   Let $P=F[x_{i,j}]$ with $n>0$, and let $P^b$ have nonnegative row basis shifts $b_i$ and column basis shifts zero. For any row-graded submodule $L$, construct $L^\sharp=\operatorname{in}(L)$ using lexicographic column degrees and set $M=P^b/L$, $M^\sharp=P^b/L^\sharp$. Then $M^\sharp$ is row-column graded and
--   $$K_{M^\sharp_{\rm row}}^P(z)=K_M^P(z).$$
--   This uses the actual initial-module construction in the source, including $L=\operatorname{im}A$. The same construction is used for the annihilator statement.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: graded modules and degree-preserving maps → actual modules with specified subspaces, an internal direct-sum predicate, and actual linear maps; reason: these are the ordinary graded-module axioms; resolution existence, K identities, and specialization exactness are separate conclusions
--   - encoding: Laurent polynomials in d variables → integer additive monoid algebra on ℤ^d; reason: exponent vectors can be negative; multiplication adds exponents and no infinite series coefficients are used
--   - generalization: existence of a row-column replacement in the source annihilated-module setting → the canonical initial replacement for every row-graded relation submodule L; reason: the construction and dimension argument on pp.22–23 require only first-degree homogeneity and do not use the annihilator; every source module has such a homogeneous finite presentation
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.17, with its construction on pp.22–23, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Cokernels

noncomputable section

namespace DetSupportRank.DeterminantSupport

/-- Lemma 5.17, p.22 and its canonical initial-module construction, pp.22–23.
Stated for arbitrary first-graded relations; the fixed matrix cokernel is included. -/
theorem lemma_5_17 {K : Type*} [Field K] {n N : ℕ} (hn : 0 < n)
    (b : Fin N → Fin n → ℕ)
    (L : Submodule (MvPolynomial (Fin n × Fin n) K)
      (Fin N → MvPolynomial (Fin n × Fin n) K))
    (hL : IsGradedSubmodule rowWeight (integerShifts b) L) :
    IsGraded (pairDegrees rowWeight columnWeight)
      (quotientModuleData (pairDegrees rowWeight columnWeight)
        (fun i => Sum.elim (integerShifts b i) (fun _ => 0))
        (initialModule rowWeight columnWeight (integerShifts b) (fun _ _ => 0) L)) ∧
    kPolynomial rowWeight
      (quotientModuleData rowWeight (integerShifts b)
        (initialModule rowWeight columnWeight (integerShifts b) (fun _ _ => 0) L)) =
    kPolynomial rowWeight (quotientModuleData rowWeight (integerShifts b) L) := by sorry

end DetSupportRank.DeterminantSupport
