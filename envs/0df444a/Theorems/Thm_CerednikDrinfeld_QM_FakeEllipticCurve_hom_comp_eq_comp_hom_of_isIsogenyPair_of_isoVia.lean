-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hom_comp_eq_comp_hom_of_isIsogenyPair_of_isoVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.hom_comp_eq_comp_hom_of_isIsogenyPair_of_isoVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/f36483d8-41c4-589d-8675-2495776f7624
-- title:
--   Intertwining of forward isogenies forces intertwining of backwards
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and assume that the image of every integer lies in $\Lambda$; let $n$ be a non-zero natural number and $T$ a commutative ring. Let $E',A',E'',A''$ be objects of `FakeEllipticCurve Λ N T`, that is, schemes over $\operatorname{Spec} T$ carrying a commutative relative group law, the smooth–proper–connected-fibres bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base compatible with the group law and with addition and multiplication in $\Lambda$, the trace normalisation, and level data. Let $\varphi : E'.A \to A'.A$ and $\varphi' : A'.A \to E'.A$ form an isogeny pair of degree $n$ in the sense of `IsIsogenyPair`: both are morphisms over $\operatorname{Spec} T$, both induce homomorphisms for the relative group laws on points over any test base, both commute with the $\Lambda$-action, and, for any witness that the image of $n$ lies in $\Lambda$, $\varphi$ followed by $\varphi'$ is the action of $n$ on $E'$ and $\varphi'$ followed by $\varphi$ is the action of $n$ on $A'$; let $\psi,\psi'$ be such a pair of degree $n$ for $E'',A''$. Let $i_E : E'.A \cong E''.A$ and $i_A : A'.A \cong A''.A$ be isomorphisms whose forward maps lie over $\operatorname{Spec} T$, each satisfying `IsoVia`, i.e. the forward map is a homomorphism for the group laws on points, intertwines the $\Lambda$-actions, and a point factors through the level morphism of the source exactly when its image factors through that of the target. Assume $i_E$ followed by $\psi$ equals $\varphi$ followed by $i_A$. Then $i_A$ followed by $\psi'$ equals $\varphi'$ followed by $i_E$.
--
--   This is the standard rigidity statement that the backward map of an isogeny pair of non-zero degree is determined by the forward map, so that an isomorphism of fake elliptic curves compatible with the forward isogenies is automatically compatible with the backward ones. It is used in the construction of the moduli-theoretic parametrisation of degree-$n$ $\Lambda$-isogeny pairs of fake elliptic curves, in the assembly of the representability statement `exists_locallyOfFinitePresentation_represents_isIsogenyPair_preservesLevel_of_closedImmersionBySections_of_intCast_mem`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hom_comp_eq_comp_hom_of_isIsogenyPair_of_isoVia.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hom_comp_eq_comp_hom_of_isIsogenyPair_of_isoVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : n ≠ 0)
    (T : Type) [CommRing T] (E' A' E'' A'' : FakeEllipticCurve Λ N T)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hp : FakeEllipticCurve.IsIsogenyPair n E' A' φ φ')
    (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hq : FakeEllipticCurve.IsIsogenyPair n E'' A'' ψ ψ')
    (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f)
    (hvE : FakeEllipticCurve.IsoVia E' E'' iE hiE) (hvA : FakeEllipticCurve.IsoVia A' A'' iA hiA)
    (h : iE.hom ≫ ψ = φ ≫ iA.hom) :
    iA.hom ≫ ψ' = φ' ≫ iE.hom := by sorry
