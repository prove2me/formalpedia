-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/62d0b95a-7332-51c4-b2d1-b3aa5f8ec35a
-- title:
--   Descent of fake elliptic curves over ℚ̄ to a number field
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is finitely generated, let $N$ be a natural number, and let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, that is, an element of the project's structure `FakeEllipticCurve`: a scheme $A$ with a morphism $f\colon A\to\operatorname{Spec}\bar{\mathbb{Q}}$, a relative group law $L$ on the functor of points of $f$ (a natural, associative, unital, invertible multiplication on $T$-points over the base for every test scheme $T$) which is commutative, the bundle of properties asserting that $f$ is smooth and proper with connected fibres and admits a relative group law, fibres of topological Krull dimension $2$, an action `act` of $\Lambda$ by endomorphisms of $A$ over the base which are additive in the element of $\Lambda$, satisfy $\mathrm{act}(xy)=\mathrm{act}(y)$ followed by $\mathrm{act}(x)$ and $\mathrm{act}(1)=\mathrm{id}$, respect the group law, and obey the trace condition $\operatorname{tr}(\mathrm{act}(m))=n$ on tangent spaces at the identity whenever $m+\bar m=n$, together with the remaining data of a scheme $C$ and a morphism `lev` into $A$ subject to the further level-$N$ conditions. Then there exist an intermediate field $K$ between $\mathbb{Q}$ and $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$ and a fake elliptic curve $E_0$ of type $(\Lambda,N)$ over $K$ such that `FakeEllipticCurve.IsPullback` holds for the inclusion $K\hookrightarrow\bar{\mathbb{Q}}$, $E_0$ and $E$: there is a morphism $g\colon E.A\to E_0.A$ making $E.f$, $E_0.f$ and $\operatorname{Spec}$ of the inclusion a pullback square, compatible with the two group laws on points of arbitrary test schemes, intertwining the two $\Lambda$-actions ($E.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $E_0.\mathrm{act}(x)$ for all $x\in\Lambda$), and carrying every point factoring through $E.\mathrm{lev}$ to a point factoring through $E_0.\mathrm{lev}$.
--
--   This is the descent of a fake elliptic curve over $\bar{\mathbb{Q}}$, with its quaternionic action and level-$N$ datum, to a model over a number field, obtained from the expression of $\bar{\mathbb{Q}}$ as the filtered union of its finite extensions of $\mathbb{Q}$ and the finite presentation of all the data involved; the hypothesis that $\Lambda$ be finitely generated makes the action descend after finitely many steps. It feeds the passage to integral models over valuation rings in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : Λ.FG) (N : ℕ)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (E₀ : FakeEllipticCurve Λ N K),
      FakeEllipticCurve.IsPullback (algebraMap K (AlgebraicClosure ℚ)) E₀ E := by sorry
