-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_forall_corr_mul_pow_eq_of_forall_isIdempotentElem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_forall_corr_mul_pow_eq_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/1560d7d4-e694-5e47-b72c-82ce54bb0449
-- title:
--   Uniform degree relation for correspondences of rigidified fake elliptic curves
-- statement:
--   Fix natural numbers $r$ (prime) and $N\neq 0$ with $r\nmid N$, and a prime $\bar r\neq r$. Let $\mathcal O$ be a commutative ring and $\pi\in\mathcal O$ an element with $(\pi)=(r)$, and let $O^{\mathrm{nr}}$ be an $\mathcal O$-algebra. Let $a,b\in\mathbb Q$ satisfy `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $v$ lies over $r$ or over $\bar r$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders and contains all rational integers, and let `coord` be a map $\Lambda\to \mathbb{W}(\mathbb F_{r^2})^2$ satisfying `IsOrderCoord Λ r coord` (additive, sending $1$ to $(1,0)$, multiplicative for the Frobenius-twisted product law on pairs, injective, with dense image in the $r$-adic sense, and compatible with reduced traces). Let $A_0$ be a fake elliptic curve of level $N$ for $\Lambda$ over $O^{\mathrm{nr}}/(\pi)$: an abelian scheme of relative dimension $2$ with commutative relative group law, $\Lambda$-action by group-law endomorphisms subject to the trace condition, and level structure. Let $T$ be an $\mathcal O$-algebra with a structural $\mathcal O$-algebra map $\psi_T:O^{\mathrm{nr}}\to T$, such that $\pi$ maps to $0$ in $T$ and every idempotent of $T$ equals $0$ or $1$. Let $E,E'$ be fake elliptic curves of level $N$ over $T$, equipped with rigidifications $\rho$, $\rho'$ with respect to $r$, $\pi$, $A_0$ and $\psi_T$; each such rigidification consists of the reduction $E_b$ over $T/(\pi)$ together with the comparison morphism exhibiting it as a pullback, a fake elliptic curve $A_b$ over $T/(\pi)$ presented as a pullback of $A_0$, an exponent $d$, and a pair of mutually dual isogenies $\varphi:E_b\to A_b$, $\varphi'$ of degree $r^d$ preserving the level structure. The assertion is that there exist positive natural numbers $F,F'$ and a natural number $c>1$, depending only on these data over $T$, with the following property. For every nontrivial $\mathcal O$-algebra $L$, every $\mathcal O$-algebra map $f:T\to L$, every fake elliptic curves $E_L,E'_L$ of level $N$ over $L$ together with morphisms $g:E_L\to E$ and $g':E'_L\to E'$ exhibiting $E_L$, $E'_L$ as pullbacks of $E$, $E'$ along $f$ (compatibly with the group laws, the $\Lambda$-actions and the level structures), every rigidifications $\rho_L$, $\rho'_L$ of $E_L$, $E'_L$ over $f\circ\psi_T$ that are pullbacks of $\rho$, $\rho'$ along $f$ via $g$, $g'$ (so in particular they have the same exponent $d$ and their isogenies correspond), every isomorphism $i_0:E_L\cong E'_L$ over $L$, every morphism $i_b:\rho_L.E_b\to\rho'_L.E_b$ compatible with $i_0$ through the comparison morphisms and over $L/(\pi)$, every morphism $u_A:\rho'_L.A_b\to\rho_L.A_b$ exhibiting $\rho'_L.A_b$ as a pullback of $\rho_L.A_b$ along the identity and satisfying $\rho_L.g_A\circ u_A=\rho'_L.g_A$, and all exponents $i_1,j_1\in\mathbb N$: if the composite of $i_b$, $\rho'_L.\varphi$, $u_A$ and the action of $r^{i_1}\in\Lambda$ on $\rho_L.A_b$ equals the composite of $\rho_L.\varphi$ with the action of $r^{j_1}$, then $F'c^{i_1}=Fc^{j_1}$.
--
--   This is the constancy step in the passage from local to global correspondences between rigidified fake elliptic curves: the degrees $F$, $F'$ of the two rigidifying isogenies and the degree $c$ of multiplication by $r$ are locally constant on $\operatorname{Spec} T$, hence constant because $T$ has no idempotents other than $0$ and $1$, so a single numerical relation between the exponents $i_1$, $j_1$ holds simultaneously over all base changes $L$ of $T$. It feeds the comparison of rigidified pairs with the same point in the presented-point model, used in the Čerednik–Drinfeld description of the bad-reduction fibre of a Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_forall_corr_mul_pow_eq_of_forall_isIdempotentElem.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_forall_corr_mul_pow_eq_of_forall_isIdempotentElem
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (T : Type) [CommRing T] [Algebra 𝒪 T] (ψT : Onr →ₐ[𝒪] T) (h0 : algebraMap 𝒪 T π = 0)
    (hTc : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1)
    (E E' : FakeEllipticCurve Λ N T)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT E') :
    ∃ (F F' c : ℕ), 0 < F ∧ 0 < F' ∧ 1 < c ∧
      ∀ (L : Type) [CommRing L] [Algebra 𝒪 L] [Nontrivial L] (f : T →ₐ[𝒪] L)
        (EL E'L : FakeEllipticCurve Λ N L)
        (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (f : T →+* L) E EL g)
        (g' : E'L.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia (f : T →+* L) E' E'L g')
        (ρL : FakeEllipticCurve.Rigidification r π A₀ (f.comp ψT) EL)
        (ρ'L : FakeEllipticCurve.Rigidification r π A₀ (f.comp ψT) E'L)
        (_ : FakeEllipticCurve.Rigidification.IsPullbackVia f g hg ρ ρL)
        (_ : FakeEllipticCurve.Rigidification.IsPullbackVia f g' hg' ρ' ρ'L)
        (i₀ : EL.A ≅ E'L.A) (_ : i₀.hom ≫ E'L.f = EL.f)
        (ib : ρL.Eb.A ⟶ ρ'L.Eb.A) (_ : ib ≫ ρ'L.gb = ρL.gb ≫ i₀.hom) (_ : ib ≫ ρ'L.Eb.f = ρL.Eb.f)
        (uA : ρ'L.Ab.A ⟶ ρL.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρL.Ab ρ'L.Ab uA) (_ : uA ≫ ρL.gA = ρ'L.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'L.φ ≫ uA ≫ ρL.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρL.φ ≫ ρL.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ →
          F' * c ^ i₁ = F * c ^ j₁ := by sorry
