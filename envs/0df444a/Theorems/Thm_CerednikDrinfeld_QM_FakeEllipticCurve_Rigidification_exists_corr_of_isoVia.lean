-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isoVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isoVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/c4579ad3-d6ea-57d4-ba93-4623c4ef3439
-- title:
--   Transport of a rigidification along an isomorphism
-- statement:
--   Fix natural numbers $r,N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{nr}$, rationals $a,b$ and a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing every rational integer (the hypothesis $h_{\Lambda\mathbb Z}$), a fake elliptic curve $A_0$ over $O^{nr}/(\pi)$ for $\Lambda$ and level $N$, an $\mathcal O$-algebra $B$, an $\mathcal O$-algebra map $\psi:O^{nr}\to B$, and fake elliptic curves $E,E'$ over $B$. Let $\varrho$ be a rigidification of $E$ relative to $(r,\pi,A_0,\psi)$, i.e. data consisting of a curve $\varrho.E_b$ over $B/(\pi)$ with $g_b$ exhibiting it as a pull-back of $E$ along $B\to B/(\pi)$ (cartesian square, compatibly with group law, $\Lambda$-action and level), a curve $\varrho.A_b$ over $B/(\pi)$ with $g_A$ exhibiting it as a pull-back of $A_0$ along $O^{nr}/(\pi)\to B/(\pi)$, an exponent $d$, and maps $\varphi,\varphi'$ forming an isogeny pair of degree $r^d$ between $\varrho.E_b$ and $\varrho.A_b$ preserving the level. Let $i:E.A\cong E'.A$ be an isomorphism over $\operatorname{Spec}B$ ($i.\mathrm{hom}$ followed by $E'.f$ equals $E.f$) which is an isomorphism of fake elliptic curves in the sense of `IsoVia`: pushing points forward along $i.\mathrm{hom}$ is a homomorphism for the relative group laws, $i.\mathrm{hom}$ intertwines the $\Lambda$-actions, and a point factors through $E.\mathrm{lev}$ if and only if its image factors through $E'.\mathrm{lev}$. Then there exist a rigidification $\varrho'$ of $E'$ relative to the same data, a map $i_b:\varrho.E_b.A\to\varrho'.E_b.A$ with $i_b$ followed by $\varrho'.g_b$ equal to $\varrho.g_b$ followed by $i.\mathrm{hom}$ and $i_b$ followed by $\varrho'.E_b.f$ equal to $\varrho.E_b.f$, a map $u_A:\varrho'.A_b.A\to\varrho.A_b.A$ which exhibits $\varrho'.A_b$ as a pull-back of $\varrho.A_b$ along the identity of $B/(\pi)$ and satisfies $u_A$ followed by $\varrho.g_A$ equal to $\varrho'.g_A$, and natural numbers $i_1,j_1$ such that $i_b$ followed by $\varrho'.\varphi$, $u_A$ and the action of $r^{i_1}\in\Lambda$ on $\varrho.A_b$ equals $\varrho.\varphi$ followed by the action of $r^{j_1}$.
--
--   This is the transport of rigidification data (in the sense used in the Čerednik–Drinfeld uniformisation of Shimura curves) across an isomorphism of the underlying fake elliptic curve, in the precise shape of comparison data needed to conclude that the two rigidified pairs have the same image under the moduli map. It is cited in the construction of lifts for the fine moduli problem and in the comparison of rigidified pair classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isoVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isoVia
    {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E E' : FakeEllipticCurve Λ N B}
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hvia : FakeEllipticCurve.IsoVia E E' i hi) :
    ∃ (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
      (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
      (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
      (i₁ j₁ : ℕ),
      ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
