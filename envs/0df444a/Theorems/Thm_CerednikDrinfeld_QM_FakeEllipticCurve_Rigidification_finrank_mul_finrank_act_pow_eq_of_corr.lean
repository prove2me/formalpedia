-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/03143c58-150f-5518-a45b-b943f12fe2bc
-- title:
--   Pointwise rank shift along an r-power correspondence
-- statement:
--   Fix a prime $r$ and a natural number $N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{\mathrm{nr}}$, rationals $a,b$, and a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q,a,b]$ containing the image of every rational integer (hypothesis `hΛℤ`); let $A_0$ be a fake elliptic curve for $(\Lambda,N)$ over $O^{\mathrm{nr}}/(\pi)$. Let $L$ be an $\mathcal O$-algebra, $\psi_L:O^{\mathrm{nr}}\to L$ an $\mathcal O$-algebra map, $E,E'$ fake elliptic curves over $L$, and $\varrho,\varrho'$ rigidifications of them relative to $r,\pi,A_0,\psi_L$: each supplies a curve $E_b$ over $L/(\pi)$ pulled back from $E$, a curve $A_b$ over $L/(\pi)$ pulled back from $A_0$ along the map induced by $\psi_L$, an exponent $d$, and morphisms $\varphi:E_b\to A_b$, $\varphi'$ forming a $\Lambda$-equivariant isogeny pair of degree $r^{d}$ with $\varphi$ preserving the level structure. Assume given an isomorphism $i_0:E.A\cong E'.A$ over $L$, a morphism $i_b:\varrho.E_b.A\to\varrho'.E_b.A$ over $L/(\pi)$ with $i_b$ followed by $\varrho'.g_b$ equal to $\varrho.g_b$ followed by $i_0$, and a morphism $u_A:\varrho'.A_b.A\to\varrho.A_b.A$ exhibiting $\varrho'.A_b$ as the pullback of $\varrho.A_b$ along the identity of $L/(\pi)$ (a pullback square compatible with the group laws, commuting with the $\Lambda$-actions, and carrying points factoring through the level morphism to such points), with $u_A$ followed by $\varrho.g_A$ equal to $\varrho'.g_A$. Assume finally, for naturals $i_1,j_1$, the relation $i_b$ followed by $\varrho'.\varphi$, $u_A$ and the action of the integer $r^{i_1}$ on $\varrho.A_b$ equals $\varrho.\varphi$ followed by the action of $r^{j_1}$. Then for every point $y'$ of the underlying space of $\varrho'.A_b.A$, writing $y=u_A(y')$, the rank of $\varrho'.\varphi$ at $y'$ times the $i_1$-th power of the rank at $y$ of the action of $r$ on $\varrho.A_b$ equals the rank of $\varrho.\varphi$ at $y$ times the $j_1$-th power of that same rank.
--
--   This is the degree bookkeeping step for correspondences between rigidified fake elliptic curves in the Cerednik–Drinfeld comparison: it records, pointwise on the mod-$\pi$ fibre and purely multiplicatively, how the ranks of the two rigidifying isogenies differ by the prescribed powers of the rank of multiplication by $r$. It is used in the passage from local relations to uniform exponents on strata, and by the statements producing locally constant degrees and ratio windows for the map to the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_finrank_mul_finrank_act_pow_eq_of_corr.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.finrank_mul_finrank_act_pow_eq_of_corr
    {r N : ℕ} [Fact r.Prime] (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (L : Type) [CommRing L] [Algebra 𝒪 L] (ψL : Onr →ₐ[𝒪] L) (E E' : FakeEllipticCurve Λ N L)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψL E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψL E')

    (i₀ : E.A ≅ E'.A) (hi : i₀.hom ≫ E'.f = E.f)
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hib : ib ≫ ϱ'.gb = ϱ.gb ≫ i₀.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hrel : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (y' : ↥ϱ'.Ab.A) :
    ϱ'.φ.finrank y' * ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y')) ^ i₁ =
      ϱ.φ.finrank (uA.base y') * ((ϱ.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩).finrank (uA.base y')) ^ j₁ := by sorry
