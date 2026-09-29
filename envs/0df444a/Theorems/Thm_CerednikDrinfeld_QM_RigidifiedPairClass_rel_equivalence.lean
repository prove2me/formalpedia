-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_rel_equivalence
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.rel_equivalence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/3f79c9e0-fb04-5f13-a4bf-add1060e0879
-- title:
--   The rigidified-pair relation is an equivalence relation
-- statement:
--   Fix natural numbers $r$ (prime) and $N \neq 0$ with $r \nmid N$, a further prime $\bar r \neq r$, a commutative ring $\mathcal O$ with an element $\pi$ generating the same ideal as $r$, and a commutative $\mathcal O$-algebra $O^{\mathrm{nr}}$. Let $a,b \in \mathbb Q$ satisfy `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$; let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a maximal order (an order in the sense of containing $1$, closed under multiplication, $\mathbb Q$-spanning and finitely generated, maximal among such) containing all rational integers, equipped with a coordinate map $\mathrm{coord} : \Lambda \to \mathbb Z_{p^2}(r)^2$ satisfying `IsOrderCoord` (additive, unital, multiplicative for the Frobenius-twisted law, injective, with dense image and the prescribed trace identity). Let $A_0$ be a fake elliptic curve of level $N$ over $O^{\mathrm{nr}}/(\pi)$, let $n \geq 3$ with $r \nmid n$, and let $(M, f_M, \mathrm{pt}_F)$ be a fine moduli datum in the sense of `IsFineModuli` for fake elliptic curves of level $N$ with full level-$n$ structure. Let $C$ be a Noetherian $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, with an $\mathcal O$-algebra map $\psi : O^{\mathrm{nr}} \to C$, let $X : \mathbb N \to \mathrm{Scheme}$ be a family of degree strata with structure maps $\xi_d$ to $M_C = M \times_{\operatorname{Spec} \mathcal O} \operatorname{Spec} C$, let $t_M$ assign to a curve with full level over a $C$-algebra $T$ a $T$-point of $M_C$, and let $x_{\mathrm{Of}}$ assign to such a curve together with a rigidification $\rho$ (in the sense of `FakeEllipticCurve.Rigidification`: reductions $E_b$, $A_b$ modulo $\pi$ with comparison maps to $E$ and to $A_0$, an exponent $d$, and an $r^d$-isogeny pair $\varphi, \varphi'$ preserving the level) a point of $X_{\rho.d}$ over $\operatorname{Spec}(T/\pi)$ lying over $t_M$. Assume the three laws `hx2`, `hx3`, `hx4` for the derived point rule `RigidifiedPairClass.ptX`: naturality under pull-back of pairs along $C$-algebra maps, surjectivity onto points of $\xi_d$ over $\operatorname{Spec} T$ with $\pi = 0$, and, for pairs over a fixed $T$ giving the same point, existence of an isomorphism of the curves with level together with comparison maps $i_b$, $u_A$ satisfying $i_b \mathbin{;} \rho'.\varphi \mathbin{;} u_A = \rho.\varphi$. Then for every $C$-algebra $T$ the relation `RigidifiedPairClass.Rel` on presented points $p = (t, d, x)$ — namely $p.t = q.t$ together with a finite family $f_k$ generating the unit ideal of $T/\pi$ such that over each localisation away from $f_k$ the two stratum points are presented by rigidified pairs $(u,\rho)$, $(u',\rho')$ of the respective degrees with an isomorphism $u \cong u'$ respecting the group law, the $\Lambda$-action, the level subscheme and the level-$n$ point, and with comparison data and exponents $i_1, j_1$ satisfying $i_b \mathbin{;} \rho'.\varphi \mathbin{;} u_A \mathbin{;} [r^{i_1}] = \rho.\varphi \mathbin{;} [r^{j_1}]$ — is reflexive, symmetric and transitive.
--
--   This is the verification that the local correspondence relation on presented points of the Čerednik–Drinfeld degree strata is an equivalence relation, so that the quotient by it is available as a candidate representing object. It is used in the construction of the rigidified-pair class model, being cited by [`CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top`](thm.html#CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top) and by [`CerednikDrinfeld.QM.RigidifiedPairClass.exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem`](thm.html#CerednikDrinfeld.QM.RigidifiedPairClass.exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_rel_equivalence.lean

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

theorem CerednikDrinfeld.QM.RigidifiedPairClass.rel_equivalence
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

    (hx2 : (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0).1))

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 →
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ))
    (T : Type) [CommRing T] [Algebra C T] :
    Equivalence (RigidifiedPairClass.Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf T) := by sorry
