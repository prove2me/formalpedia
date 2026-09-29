-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/d747b01e-3281-5da9-8fa0-9ba0a63d6487
-- title:
--   Drinfeld's trace condition at every geometric point of Z
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'` (that is, $0<a$ or $0<b$, and for a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$), and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order ($1\in\Lambda$, closed under multiplication, $\mathbb{Q}$-spanning, finitely generated) maximal among orders containing it. Assume given $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$ and a map $\mathrm{star}:\Lambda\to\Lambda$ with $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x$. Let $R$ be a noetherian local ring, complete for the adic topology of its maximal ideal $\mathfrak{m}$, together with ring maps $\pi_n:R/\mathfrak{m}^{n+2}\to R/\mathfrak{m}^{n+1}$ compatible with the quotient maps. Let $(E_n)_{n}$ be fake elliptic curves with $\Lambda$-action of level $1$ over $R/\mathfrak{m}^{n+1}$ and $t_n:(E_n).A\to(E_{n+1}).A$ with `FakeEllipticCurve.IsPullbackVia (π n) (E (n+1)) (E n) (t n)`: $t_n$ exhibits $(E_n).A$ as the fibre product of $(E_{n+1}).A$ with $\operatorname{Spec}(R/\mathfrak{m}^{n+1})$ over $\operatorname{Spec}(R/\mathfrak{m}^{n+2})$, compatibly with the group laws on $T$-points, with the $\Lambda$-actions and with the level morphisms. Let $Z$ be a scheme with a finite morphism $G$ to $\operatorname{Proj}$ of the homogeneous polynomials in $r+1$ variables over $R$, write $f_Z:=G$ followed by `ProjSpace.π R r`, and let $j_n:(E_n).A\to Z$ satisfy $t_n$ followed by $j_{n+1}$ equals $j_n$ and make each square $(j_n,(E_n).f,f_Z,\operatorname{Spec}(R\to R/\mathfrak{m}^{n+1}))$ a pullback. Assume $f_Z$ is smooth and smooth of relative dimension $2$, let $L$ be a relative group law on $f_Z$ over $R$, commutative, and let $\mathrm{act}:\Lambda\to\operatorname{End}(Z)$ consist of morphisms over $f_Z$ which are homomorphisms for $L$ on $T$-points, with $\mathrm{act}(1)=\mathrm{id}_Z$, $\mathrm{act}(xy)=\mathrm{act}(y)$ followed by $\mathrm{act}(x)$, and $\mathrm{act}(x+y)$ the $L$-product of $\mathrm{act}(x)$ and $\mathrm{act}(y)$ on points; assume further that each $j_n$ carries the group law of $E_n$ to $L$ and intertwines $(E_n).\mathrm{act}$ with $\mathrm{act}$. Then for every algebraically closed field $k$, every ring map $s_k:R\to k$, every finite-dimensional $k$-vector space $V$ and every injective $\tau:V\to$ points of $f_Z$ over `tangentBase k sk` whose image is exactly the set of $P$ with $\mathrm{tangentZero}\circ P=L$-identity over `geomPoint k sk`, which is additive for the $L$-product and satisfies $\tau(cv)=\mathrm{tangentScale}(c)$ followed by $\tau(v)$, and for all $m\in\Lambda$ and $k$-linear $\Phi:V\to V$ with $\tau(\Phi v)=\mathrm{act}(m)\circ\tau(v)$ and all $n\in\mathbb{Z}$ with $m+\bar m=n$ in $\mathbb{H}[\mathbb{Q},a,b]$, one has $\operatorname{tr}_k\Phi=n$ in $k$.
--
--   This is Drinfeld's trace condition — the `act_trace` axiom in the definition of a fake elliptic curve with $\Lambda$-action — verified for the quadruple $(Z,f_Z,L,\mathrm{act})$ obtained by algebraising a formal tower of fake elliptic curves over the quotients $R/\mathfrak{m}^{n+1}$: from its validity on the closed fibres it is propagated to every geometric point of $\operatorname{Spec} R$. It is used in the construction producing a fake elliptic curve over $R$ itself whose reductions are the given tower, in the Čerednik–Drinfeld description of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld
open CerednikDrinfeld.QM
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

    (π : ∀ n : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))

    (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
    (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))
    {r : ℕ}
    (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) [IsFinite G] (jz : ∀ n : ℕ, (E n).A ⟶ Z)
    (hZ :
      (∀ n, t n ≫ jz (n + 1) = jz n) ∧
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (hsmooth : Smooth (G ≫ ProjSpace.π R r)) (L : RelativeGroupLaw R (G ≫ ProjSpace.π R r))
    (act : ↥Λ → (Z ⟶ Z)) (act_over : ∀ x : ↥Λ, act x ≫ (G ≫ ProjSpace.π R r) = (G ≫ ProjSpace.π R r))

    (hmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))))
      (P Q : SchemeHomOver t' (E n).f),
      ((E n).L.mul t' P Q).1 ≫ jz n =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))
          ⟨P.1 ≫ jz n, by rw [Category.assoc, (hZ.2 n).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ jz n, by rw [Category.assoc, (hZ.2 n).w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ (n : ℕ) (x : ↥Λ), (E n).act x ≫ jz n = jz n ≫ act x)

    (hc : L.IsCommutative)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
      pushPt (act x) (act_over x) (L.mul t' P Q) = L.mul t' (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 Z)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t' (G ≫ ProjSpace.π R r)),
      pushPt (act (x + y)) (act_over (x + y)) P = L.mul t' (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))

    [SmoothOfRelativeDimension 2 (G ≫ ProjSpace.π R r)] :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) (G ≫ ProjSpace.π R r)),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) (G ≫ ProjSpace.π R r), P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
      ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k) := by sorry
