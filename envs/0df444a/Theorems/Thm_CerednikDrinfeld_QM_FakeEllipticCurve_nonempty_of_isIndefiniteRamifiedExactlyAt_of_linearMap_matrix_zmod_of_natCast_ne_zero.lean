-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/5e0f8c65-616b-52fd-b601-5f76e6b15694
-- title:
--   Existence of level-N fake elliptic curves over algebraically closed fields
-- statement:
--   Fix rationals $a,b$ and primes $q,q'$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: that $0<a$ or $0<b$, and that for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order, i.e. it contains $1$, is closed under multiplication, spans the algebra over $\mathbb Q$ and is finitely generated, and is maximal among such submodules containing it. Let $M$ and $N$ be naturals with $N\neq 0$, and let $\varphi:\Lambda\to M_2(\mathbb Z/N)$ be a $\mathbb Z$-linear map which sends $1$ to $1$, satisfies $\varphi(xy)=\varphi(x)\varphi(y)$ whenever $xy$ lies in $\Lambda$, is surjective, and has $\varphi(x)=0$ precisely when $x=N\cdot y$ for some $y\in\Lambda$; thus $\varphi$ induces a ring isomorphism $\Lambda/N\Lambda\cong M_2(\mathbb Z/N)$. Let $k$ be an algebraically closed field with $N\neq 0$ in $k$. Then, given one object $E$ of `FakeEllipticCurve Λ M k` — a scheme $A$ over $\operatorname{Spec} k$ which is smooth and proper with connected fibres of topological Krull dimension $2$, equipped with a commutative relative group law, an action of $\Lambda$ by endomorphisms over the base that is additive and multiplicative in $\Lambda$ and respects the group law, whose induced action on tangent spaces has trace the reduced trace $n$ of the acting element, together with the remaining level-$M$ data of the structure (the scheme $C$ and the morphism `lev`) — the type `FakeEllipticCurve Λ N k` is nonempty.
--
--   This is the level-changing step for fake elliptic curves (abelian surfaces with an action of a maximal order in an indefinite rational quaternion algebra of discriminant $qq'$): once one such object exists over an algebraically closed field $k$, and $N$ is invertible in $k$ with $\Lambda/N\Lambda\cong M_2(\mathbb Z/N)$, a level-$N$ structure can be installed. It is used in the construction of fake elliptic curves over an algebraic closure of $\mathbb Q$ and over algebraically closed fields of positive characteristic, which feed the Čerednik–Drinfeld description of the relevant Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {M : ℕ} (N : ℕ) [NeZero N]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφ_surj : Function.Surjective φ)
    (hφ_ker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]))
    (k : Type) [Field k] [IsAlgClosed k] (hN : (N : k) ≠ 0) (E : FakeEllipticCurve Λ M k) :
    Nonempty (FakeEllipticCurve Λ N k) := by sorry
