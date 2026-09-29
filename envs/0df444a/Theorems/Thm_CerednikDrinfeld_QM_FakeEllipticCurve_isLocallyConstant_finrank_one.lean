-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLocallyConstant_finrank_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isLocallyConstant_finrank_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/4ba889eb-7735-5a0d-be94-561cf8a1afe7
-- title:
--   Rank of a finite flat morphism: fibrewise and locally constant
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative ring $S$. Let $E$ and $A$ be fake elliptic curves of level $N$ with $\Lambda$-action over $S$ in the sense of the project's structure `FakeEllipticCurve`: each consists of a scheme with a morphism to $\operatorname{Spec} S$, a commutative relative group law on its functor of points over $\operatorname{Spec} S$ (with multiplication, unit and inverse natural in the test base), the property bundle asserting that the structure morphism is smooth and proper with connected fibres, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base compatible with the group law and subject to a trace condition on tangent spaces, together with further data. Let $\varphi : E.A \to A.A$ be a morphism of the underlying schemes with $\varphi$ followed by $A.f$ equal to $E.f$, and assume $\varphi$ is finite, flat and locally of finite presentation. The conclusion is twofold: first, for every point $y$ of the space of $A.A$, the rank $\varphi.\mathrm{finrank}$ at $y$ equals its value at the image of $A.f(y)$ under the base map of the unit section $A.L.\mathrm{one}$ taken over the identity of $\operatorname{Spec} S$; second, the function sending $s \in \operatorname{Spec} S$ to the rank of $\varphi$ at the unit point above $s$ is locally constant.
--
--   This is the statement that the rank of a finite locally free morphism between fake elliptic curves is constant on each fibre of the target over the base and locally constant on $\operatorname{Spec} S$, so that the degree strata of such a morphism are open and closed in the base. It is used in the rigidification of fake elliptic curves, where degree conditions on finite flat maps must be propagated over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLocallyConstant_finrank_one.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isLocallyConstant_finrank_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ] :
    (∀ y : ↥A.A, φ.finrank y =
        φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base (A.f.base y))) ∧
      IsLocallyConstant (fun s : ↥(Spec (CommRingCat.of S)) =>
        φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s)) := by sorry
