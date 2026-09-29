-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/244e3fca-2451-58c8-aae4-eec1f9af9bb5
-- title:
--   Corresponding rigidified isomorphisms descend to base change
-- statement:
--   Fix naturals $r,N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{nr}$, rationals $a,b$ and a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing every rational integer, and a fake elliptic curve $A_0$ for $(\Lambda,N)$ over $O^{nr}/(\pi)$. Let $\varphi:B\to B'$ be a map of $\mathcal O$-algebras and $\psi:O^{nr}\to B$ an $\mathcal O$-algebra map. Assume given fake elliptic curves $E,E'$ for $(\Lambda,N)$ over $B$, an isomorphism $i:E.A\cong E'.A$ over $\operatorname{Spec}B$ compatible with the relative group laws, with the $\Lambda$-actions and with the level (points factor through $E.\mathrm{lev}$ iff their images factor through $E'.\mathrm{lev}$), rigidifications $\varrho$ of $E$ and $\varrho'$ of $E'$ (each consisting of reductions $E_b$, $A_b$ over $B/(\pi)$ pulled back from $E$ and from $A_0$ along $\psi$, together with a level-preserving $r^d$-isogeny pair $\varphi,\varphi'$), a map $i_b:\varrho.E_b.A\to\varrho'.E_b.A$ over $B/(\pi)$ with $i_b\circ$-compatibility $i_b\ggg \varrho'.g_b=\varrho.g_b\ggg i.\mathrm{hom}$, a morphism $u_A:\varrho'.A_b.A\to\varrho.A_b.A$ exhibiting $\varrho'.A_b$ as a pullback of $\varrho.A_b$ along the identity of $B/(\pi)$ and satisfying $u_A$ followed by $\varrho.g_A$ equals $\varrho'.g_A$, and exponents $i_1,j_1$ with $i_b\ggg\varrho'.\varphi\ggg u_A\ggg\varrho.A_b.\mathrm{act}(r^{i_1})=\varrho.\varphi\ggg\varrho.A_b.\mathrm{act}(r^{j_1})$, the actions being those of the rational integers $r^{i_1},r^{j_1}\in\Lambda$. Assume further fake elliptic curves $E_\varphi,E'_\varphi$ over $B'$ with morphisms $g,g'$ exhibiting them as pullbacks of $E,E'$ along $\varphi$ (pullback square, compatibility with group laws and $\Lambda$-actions, and lifting of level points), and rigidifications $\varrho_\varphi,\varrho'_\varphi$ over $B'$ relative to $\varphi\circ\psi$ that are pullbacks of $\varrho,\varrho'$ along $\varphi$. Then there exist an isomorphism $i_\varphi:E_\varphi.A\cong E'_\varphi.A$ over $\operatorname{Spec}B'$ compatible with group laws, $\Lambda$-actions and level, satisfying $i_\varphi.\mathrm{hom}$ followed by $g'$ equals $g$ followed by $i.\mathrm{hom}$, together with data $i_{b,\varphi}$ and $u_{A,\varphi}$ of exactly the same shape as $i_b,u_A$ (the latter again a pullback along the identity of $B'/(\pi)$, compatible with the maps $g_A$), for which the correspondence identity holds with the same exponents $i_1,j_1$.
--
--   This is the base-change stability of the correspondence clause attached to a pair of rigidified fake elliptic curves in the Čerednik–Drinfeld uniformisation: an isomorphism of curves whose rigidifications correspond with given scalar exponents pulls back along any map of the base $\mathcal O$-algebras, with the exponents unchanged. It is used by the lemmas that transport rigidifications and verify the supersingular correspondence locally on the pieces of a covering, and hence by the statements producing full level structures over connected components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isPullbackVia
    {r N : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B B' : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B)

    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (Eφ : FakeEllipticCurve Λ N B') (g : Eφ.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E Eφ g)
    (E'φ : FakeEllipticCurve Λ N B') (g' : E'φ.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E' E'φ g')
    (ϱφ : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) Eφ) (hϱφ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ϱ ϱφ)
    (ϱ'φ : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E'φ) (hϱ'φ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g' hg' ϱ' ϱ'φ) :
    ∃ (iφ : Eφ.A ≅ E'φ.A) (hiφ : iφ.hom ≫ E'φ.f = Eφ.f) (_ : FakeEllipticCurve.IsoVia Eφ E'φ iφ hiφ)
      (_ : iφ.hom ≫ g' = g ≫ i.hom)
      (ibφ : ϱφ.Eb.A ⟶ ϱ'φ.Eb.A) (_ : ibφ ≫ ϱ'φ.gb = ϱφ.gb ≫ iφ.hom) (_ : ibφ ≫ ϱ'φ.Eb.f = ϱφ.Eb.f)
      (uAφ : ϱ'φ.Ab.A ⟶ ϱφ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱφ.Ab ϱ'φ.Ab uAφ) (_ : uAφ ≫ ϱφ.gA = ϱ'φ.gA),
      ibφ ≫ ϱ'φ.φ ≫ uAφ ≫ ϱφ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱφ.φ ≫ ϱφ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
