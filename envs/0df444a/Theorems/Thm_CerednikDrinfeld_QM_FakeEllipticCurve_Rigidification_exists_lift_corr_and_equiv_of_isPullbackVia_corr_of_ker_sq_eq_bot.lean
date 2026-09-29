-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/8302518a-1258-5ae2-9c7c-3828058049bc
-- title:
--   Rigidifications lift along square-zero thickenings, up to r-power scalars
-- statement:
--   Fix a prime $r$ and a nonzero level $N$ with $r \nmid N$, a commutative ring $\mathcal O$ with an element $\pi$ generating the same ideal as $r$, and a commutative $\mathcal O$-algebra $O^{\mathrm{nr}}$. Fix $a,b \in \mathbb Q$, a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ containing every rational integer, a map $\mathrm{coord} \colon \Lambda \to \mathbb W(\mathbb F_{r^2})^2$ which is `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the Frobenius-twisted law on pairs, injective, with image dense modulo every power of $r$, and compatible with reduced traces), and a fake elliptic curve $A_0$ with $\Lambda$-action and level-$N$ datum over $O^{\mathrm{nr}}/\pi$. Further data: an integer $n \ge 3$ with $r \nmid n$ and a fine moduli datum $(M, f_M, \mathrm{ptF})$ for level $(N,n)$ over $\operatorname{Spec}\mathcal O$ in the sense of `IsFineModuli` (the point map respects isomorphism, is compatible with base change, and is bijective on $S$-points for every $\mathcal O$-algebra $S$); a Noetherian $\mathcal O$-algebra $C$ in which the image of $\pi$ is nilpotent, with $\psi \colon O^{\mathrm{nr}} \to C$; Noetherian $C$-algebras $S, S_0$ compatibly over $\mathcal O$; a surjection $p \colon S \to S_0$ of $C$-algebras with $(\ker p)^2 = 0$; the induced leg $\psi_S$, equal to $\psi$ followed by $C \to S$. Finally, a full-level-$n$ fake elliptic curve $u = (E,P)$ over $S$, one $u_0 = (E_0,P_0)$ over $S_0$, a morphism $g \colon E_0 \to E$ exhibiting $E_0$ as the pullback of $E$ along $p$ (a pullback square of structure maps, compatible with the group law, the $\Lambda$-action and the level subscheme), with $P_0$ followed by $g$ equal to $\operatorname{Spec}(p)$ followed by $P$, and a rigidification $\rho_0$ of $E_0$ relative to $p \circ \psi_S$ (a curve $\rho_0.E^{\flat}$ over $S_0/\pi$ pulled back from $E_0$, a curve $\rho_0.A^{\flat}$ pulled back from $A_0$, and a level-preserving $r^{d}$-isogeny pair between them). The conclusion has two halves. First, there exist a rigidification $\rho$ of $E$ relative to $\psi_S$, a rigidification $\rho_0'$ of $E_0$ which is a pullback of $\rho$ along $p$ and $g$ in the sense of `Rigidification.IsPullbackVia`, and a correspondence between $\rho_0$ and $\rho_0'$: a morphism $ib$ of the $E^{\flat}$-parts over $E_0$ and over $S_0/\pi$, a morphism $uA$ of the $A^{\flat}$-parts exhibiting $\rho_0'.A^{\flat}$ as a pullback along the identity ring map and compatible with the maps to $A_0$, and exponents $i_1, j_1$ such that the two composites with the isogenies agree after acting by $r^{i_1}$, respectively $r^{j_1}$, through the $\Lambda$-action. Secondly, any two rigidifications $\rho, \rho'$ of $E$ whose pullbacks $\rho_0', \rho_0''$ along $p$ and $g$ both admit such a correspondence with $\rho_0$ are equivalent in the sense of `Rigidification.Equiv`, i.e. comparison maps of the $E^{\flat}$- and $A^{\flat}$-parts exist whose isogenies agree up to $r$-power scalars.
--
--   This is the deformation-theoretic step for rigidified fake elliptic curves: rigidifications of a full-level fake elliptic curve extend across a square-zero extension of the Noetherian base, and do so uniquely up to the equivalence which allows composition with $r$-power scalars. It is used in establishing that the functor of rigidified curves with full level structure is represented, in the Čerednik–Drinfeld description of the $r$-adic moduli of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_lift_corr_and_equiv_of_isPullbackVia_corr_of_ker_sq_eq_bot
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [IsNoetherianRing S₀] [Algebra C S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
    (p : S →ₐ[C] S₀) (hp : Function.Surjective p) (hp2 : RingHom.ker (p : S →+* S₀) ^ 2 = ⊥)
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u₀ : FakeEllipticCurve.WithFullLevel Λ N n S₀)
    (g : u₀.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (p : S →+* S₀) u.1 u₀.1 g)
    (hgP : (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ (u.2.P).1)
    (ρ₀ : FakeEllipticCurve.Rigidification r π A₀ ((p.restrictScalars 𝒪).comp ψS) u₀.1) :

    (∃ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ₀' : FakeEllipticCurve.Rigidification r π A₀ ((p.restrictScalars 𝒪).comp ψS) u₀.1)
        (_ : FakeEllipticCurve.Rigidification.IsPullbackVia (p.restrictScalars 𝒪) g hg ρ ρ₀'),
        ∃ (ib : ρ₀.Eb.A ⟶ ρ₀'.Eb.A) (_ : ib ≫ ρ₀'.gb = ρ₀.gb ≫ (Iso.refl u₀.1.A).hom) (_ : ib ≫ ρ₀'.Eb.f = ρ₀.Eb.f)
          (uA : ρ₀'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ₀'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ₀'.gA)
          (i₁ j₁ : ℕ),
          ib ≫ ρ₀'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧

    (∀ (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ₀' ρ₀'' : FakeEllipticCurve.Rigidification r π A₀ ((p.restrictScalars 𝒪).comp ψS) u₀.1),
        FakeEllipticCurve.Rigidification.IsPullbackVia (p.restrictScalars 𝒪) g hg ρ ρ₀' →
        FakeEllipticCurve.Rigidification.IsPullbackVia (p.restrictScalars 𝒪) g hg ρ' ρ₀'' →
        (∃ (ib : ρ₀.Eb.A ⟶ ρ₀'.Eb.A) (_ : ib ≫ ρ₀'.gb = ρ₀.gb ≫ (Iso.refl u₀.1.A).hom) (_ : ib ≫ ρ₀'.Eb.f = ρ₀.Eb.f)
          (uA : ρ₀'.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ₀'.Ab uA) (_ : uA ≫ ρ₀.gA = ρ₀'.gA)
          (i₁ j₁ : ℕ),
          ib ≫ ρ₀'.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
        (∃ (ib : ρ₀.Eb.A ⟶ ρ₀''.Eb.A) (_ : ib ≫ ρ₀''.gb = ρ₀.gb ≫ (Iso.refl u₀.1.A).hom) (_ : ib ≫ ρ₀''.Eb.f = ρ₀.Eb.f)
          (uA : ρ₀''.Ab.A ⟶ ρ₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₀.Ab ρ₀''.Ab uA) (_ : uA ≫ ρ₀.gA = ρ₀''.gA)
          (i₁ j₁ : ℕ),
          ib ≫ ρ₀''.φ ≫ uA ≫ ρ₀.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₀.φ ≫ ρ₀.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
        FakeEllipticCurve.Rigidification.Equiv hΛℤ ρ ρ') := by sorry
