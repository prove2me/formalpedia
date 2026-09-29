-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_forall_factorsThrough_iff_of_isOrder
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_forall_factorsThrough_iff_of_isOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/6411261a-3ede-58b9-8625-f8540e427e29
-- title:
--   Extra levels with equal ℚ̄-points give isomorphic quotients
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a nonzero natural number $N$, and a natural number $\ell$ assumed prime; assume [`QuaternionAlgebra.IsOrder Λ`](def/QuaternionAlgebra_Order.html#L11), i.e. $\Lambda$ contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$ and is finitely generated. Let $E$ be a `FakeEllipticCurve Λ N` over $\overline{\mathbb{Q}}$: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec}\overline{\mathbb{Q}}$, a commutative relative group law, an abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by base-preserving endomorphisms that is additive and multiplicative with the prescribed trace condition, and a level-$N$ subscheme $E.\mathrm{lev}$. Let $K,K'$ be extra levels at $\ell$ on $E$, that is closed immersions $K.\mathrm{levK}\colon K.K\to E.A$ whose factoring points form a subgroup annihilated by $\ell$, stable under $\Lambda$, meeting the points of $E.\mathrm{lev}$ only in the identity, with $K.\mathrm{levK}$ composed with $E.f$ finite, flat and locally of finite presentation of fibre rank $\ell^2$, and with geometric fibres $\mathbb{Z}/\ell\times\mathbb{Z}/\ell$ as groups. Assume that for every point $x$ of $E$ over the identity of $\operatorname{Spec}\overline{\mathbb{Q}}$ (a section of $E.f$), $x$ factors through $K.\mathrm{levK}$ if and only if it factors through $K'.\mathrm{levK}$. Let $d,d'$ be fake elliptic curves of the same type and suppose `IsLevelIsogeny ℓ ⟨E,K⟩ d` and `IsLevelIsogeny ℓ ⟨E,K'⟩ d'`: there are base-preserving morphisms $\varphi$ and $\psi$ in both directions compatible with the group laws and with the $\Lambda$-actions, whose two composites are the action of $\ell$ whenever $\ell$ lies in $\Lambda$, such that a point of $E$ is killed by $\varphi$ exactly when it factors through the corresponding $\mathrm{levK}$, and $\varphi$ carries $E.\mathrm{lev}$-points to level points of the target. The conclusion is `FakeEllipticCurve.Iso d d'`: an isomorphism $d.A\cong d'.A$ over $\operatorname{Spec}\overline{\mathbb{Q}}$ compatible with the group laws, commuting with the $\Lambda$-actions, and matching the points factoring through the level subschemes.
--
--   In characteristic zero a finite subgroup scheme of an abelian variety is determined by its geometric points, so two extra levels at $\ell$ with the same $\overline{\mathbb{Q}}$-points have isomorphic quotients; this is the rigidity statement needed to compare the moduli-theoretic description of the Hecke correspondence on a quaternionic curve with its description via the tower. It is used in the construction of the uniformised Hecke curve and in the accompanying counting statements about fake elliptic curves with extra level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_forall_factorsThrough_iff_of_isOrder.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open AlgebraicCurve
open CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_forall_factorsThrough_iff_of_isOrder
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] (ℓ : ℕ) (hℓ : ℓ.Prime) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (K K' : E.ExtraLevel ℓ)
    (hKK' : ∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
      FactorsThrough K.levK x ↔ FactorsThrough K'.levK x)
    (d d' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (hd : FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E, K⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d)
    (hd' : FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E, K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d') :
    FakeEllipticCurve.Iso d d' := by sorry
