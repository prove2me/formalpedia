-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_zmod_mul_prod_equiv_factorsThrough_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0e73f4e4-dec5-5462-ae67-8fc5cdac3d05
-- title:
--   Geometric fibre of the combined level structure is (ℤ/Nℓ)²
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and natural numbers $N,\ell$ with $\gcd(N,\ell)=1$. Let $S$ be a commutative ring and let $u$ be an element of `FakeEllipticCurve.WithExtraLevel Λ N ℓ S`, that is, a pair consisting of a fake elliptic curve $u.1$ over $S$ — an abelian scheme $f : A \to \operatorname{Spec} S$ with relative group law $L$, a $\Lambda$-action, and a level structure $u.1.\mathrm{lev} : u.1.C \to A$ — together with an extra level structure $u.2$ at $\ell$, whose data include a closed immersion $u.2.\mathrm{levK} : K \to A$ cutting out a subgroup of $\ell$-torsion points of fibre rank $\ell^2$. Let $C'$ be a scheme and $\mathrm{lev}' : C' \to A$ a morphism such that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $T$-point $P$ of $A$ over $t$ (a morphism $T \to A$ composing with $f$ to $t$), $P$ factors through $\mathrm{lev}'$ — i.e. $P$ is $P_0$ followed by $\mathrm{lev}'$ for some $P_0 : T \to C'$ — if and only if the $\ell$-fold multiple $\ell\cdot P$ (iterated $L$-multiplication) factors through $u.1.\mathrm{lev}$ and the $N$-fold multiple $N\cdot P$ factors through $u.2.\mathrm{levK}$. Let $k$ be an algebraically closed field, $sk : S \to k$ a ring homomorphism, and suppose $N\ell \neq 0$ in $k$. Then there is a bijection $e$ from $\mathbb{Z}/N\ell \times \mathbb{Z}/N\ell$ onto the set of $k$-points of $A$ over the geometric point $\operatorname{Spec} k \to \operatorname{Spec} S$ induced by $sk$ which factor through $\mathrm{lev}'$, satisfying $e(x+y) = L.\mathrm{mul}(e(x), e(y))$ for all $x,y$.
--
--   This computes the geometric fibres of the combined level structure $C' = [\ell]^{-1}(C) \cap [N]^{-1}(K)$ attached to a level-$N$ structure together with an extra level structure at $\ell$: over an algebraically closed field in which $N\ell$ is invertible its points form a group isomorphic to $(\mathbb{Z}/N\ell)^2$, via the Chinese remainder theorem applied to the level-$N$ and level-$\ell$ fibres. It feeds the construction of a fake elliptic curve of level $N\ell$ out of such a pair, cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_zmod_mul_prod_equiv_factorsThrough_of_coprime
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    {C' : Scheme.{0}} (lev' : C' ⟶ u.1.A)
    (hlev' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough lev' P ↔
        FactorsThrough u.1.lev (nsmulPt u.1.L t ℓ P) ∧ FactorsThrough u.2.levK (nsmulPt u.1.L t N P))
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hk : ((N * ℓ : ℕ) : k) ≠ 0) :
    ∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (geomPoint k sk) u.1.f // FactorsThrough lev' P},
      ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
        (e (x + y) : SchemeHomOver (geomPoint k sk) u.1.f) = u.1.L.mul (geomPoint k sk) (e x) (e y) := by sorry
