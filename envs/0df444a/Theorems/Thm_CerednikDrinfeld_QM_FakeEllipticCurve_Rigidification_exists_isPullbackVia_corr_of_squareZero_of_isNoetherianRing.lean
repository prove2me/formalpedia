-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/1efc0536-7c38-5799-975b-d378dd4d53ef
-- title:
--   Lifting rigidifications along a square-zero thickening
-- statement:
--   Fix a prime $r$ and a level $N \ge 1$ with $r \nmid N$, a commutative ring $\mathcal O$ and an element $\pi \in \mathcal O$ with $(\pi) = (r)$, and an $\mathcal O$-algebra $O^{\mathrm{nr}}$. Let $\Lambda$ be a $\mathbb Z$-submodule of the rational quaternion algebra $\mathbb H[\mathbb Q,a,b]$ containing every integer, equipped with a map $\mathrm{coord} : \Lambda \to W(\mathbb F_{r^2})^2$ satisfying `IsOrderCoord`: additive, sending $1$ to $(1,0)$, multiplicative for the twisted rule $(\alpha_1\alpha_2 + r\,\beta_1 F\beta_2,\ \alpha_1\beta_2 + \beta_1 F\alpha_2)$, injective, with image dense for the $r$-adic filtration, and with first coordinate plus its Frobenius equal to the reduced trace. Let $A_0$ be a fake elliptic curve of level $N$ over $O^{\mathrm{nr}}/\pi$ (an abelian scheme with commutative relative group law, all fibres of dimension $2$, a $\Lambda$-action compatible with the group law and satisfying the trace condition, and a level-$N$ datum). Let $p : B \to B_0$ be a surjective morphism of $\mathcal O$-algebras with $B$ Noetherian whose kernel is square-zero (any two elements killed by $p$ have zero product), let $\psi : O^{\mathrm{nr}} \to B$ be an $\mathcal O$-algebra map, and assume $N$ is invertible in $B/\pi$. Let $E$ and $E_0$ be fake elliptic curves of level $N$ over $B$ and $B_0$, and $g : E_0.A \to E.A$ a morphism exhibiting $E_0$ as the pullback of $E$ along $p$ in the sense of `FakeEllipticCurve.IsPullbackVia` (cartesian square over $\mathrm{Spec}$, compatible with the group laws and the $\Lambda$-actions, and carrying level points to level points). Finally let $\rho_0$ be a rigidification of $E_0$ relative to $(A_0, p \circ \psi)$, that is, reductions $E_{0,b}$ of $E_0$ and $A_{0,b}$ of $A_0$ over $B_0/\pi$ together with a level-preserving isogeny pair of degree $r^{d}$ between them. The conclusion asserts the existence of a rigidification $\rho$ of $E$ relative to $(A_0,\psi)$ and a rigidification $\rho'$ of $E_0$ relative to $(A_0, p\circ\psi)$ with $\rho'$ a pullback of $\rho$ along $p$ in the sense of `Rigidification.IsPullbackVia` (comparison maps on the reductions and on the $A$-sides compatible with $g$, $\rho.gb$, $\rho.gA$, equal isogeny exponents, and $u_b \circ$-compatibility of the two $\varphi$'s), together with a morphism $i_b : \rho_0.Eb.A \to \rho'.Eb.A$ over $B_0/\pi$ satisfying $i_b$ followed by $\rho'.gb$ equals $\rho_0.gb$, a morphism $u_A : \rho'.Ab.A \to \rho_0.Ab.A$ identifying $\rho'.Ab$ with $\rho_0.Ab$ as a pullback along the identity of $B_0/\pi$ and satisfying $u_A$ followed by $\rho_0.gA$ equals $\rho'.gA$, and natural numbers $i_1, j_1$ with $i_b$ followed by $\rho'.\varphi$, then $u_A$, then the action of $r^{i_1} \in \Lambda$ on $\rho_0.Ab$ equal to $\rho_0.\varphi$ followed by the action of $r^{j_1}$; so the two rigidifications agree only after multiplication by powers of $r$.
--
--   This is the existence half of Drinfeld's rigidity property for quasi-isogenies in the Čerednik–Drinfeld setting: a rigidification of the reduction of a fake elliptic curve over a square-zero thickening $B \twoheadrightarrow B_0$ lifts to a rigidification upstairs, uniquely up to $r$-power scalars. It is used in the construction of liftings of rigidified pairs and in the local lifting step for fine families of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_corr_of_squareZero_of_isNoetherianRing
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀) (hp : Function.Surjective p) (hp2 : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ : Onr →ₐ[𝒪] B) (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)
    (ρ₀ : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀) :
    ∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
      (_ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ρ ρ'),
      ∃ (ib : ρ₀.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ₀.gb ≫ (Iso.refl E₀.A).hom) (_ : ib ≫ ρ'.Eb.f = ρ₀.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
