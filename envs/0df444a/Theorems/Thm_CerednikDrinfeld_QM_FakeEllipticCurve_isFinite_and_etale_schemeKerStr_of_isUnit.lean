-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/d4a7ceee-e99d-54f1-b346-2498e6c0ce37
-- title:
--   m-torsion of a fake elliptic curve is finite étale
-- statement:
--   Let $a,b$ be rational numbers, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N$ be a natural number and let $S$ be a commutative ring. Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$: this packages a scheme $E.A$ with a morphism $E.f : E.A \to \operatorname{Spec} S$, a relative group law $E.L$ on $E.f$ (a functorial group structure on $T$-points over $\operatorname{Spec} S$, compatible with base change) which is commutative, the bundle of properties asserting that $E.f$ is smooth and proper with connected fibres and admits a relative group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ on $E.A$ over $S$ which is additive and multiplicative and satisfies the trace condition relating $\operatorname{tr}(\Phi)$ on tangent spaces to $m + \bar m$, together with the further curve and level-$N$ data of the structure. Let $m$ be a natural number whose image in $S$ is a unit. Then the morphism $E.L.\mathrm{schemeKerStr}\,m$ — the second projection to $\operatorname{Spec} S$ of the pullback of the multiplication-by-$m$ morphism $E.L.\mathrm{schemeNsmul}\,m : E.A \to E.A$ along the unit section of $E.L$ over $\operatorname{Spec} S$ — is both finite and étale.
--
--   This is the standard statement that the kernel of multiplication by $m$ on an abelian scheme is a finite étale group scheme over the base as soon as $m$ is invertible there, here for the abelian surfaces with quaternionic multiplication that serve as fake elliptic curves. It is used in the construction of full level-$m$ structures on such curves, and through that in the comparison of the quaternionic moduli problem with its level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ) (hm : IsUnit ((m : ℕ) : S)) :
    IsFinite (E.L.schemeKerStr m) ∧ Etale (E.L.schemeKerStr m) := by sorry
