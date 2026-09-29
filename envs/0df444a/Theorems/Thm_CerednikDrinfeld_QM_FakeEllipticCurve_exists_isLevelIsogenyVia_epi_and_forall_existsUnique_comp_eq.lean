-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/4fbe72d6-1858-587f-8e6b-3f05b2dc22c8
-- title:
--   Quotient of a fake elliptic curve by an extra level
-- statement:
--   Fix primes $r$ and $\bar r$ with $\bar r \neq r$, a nonzero natural number $N$, and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it and which contains all rational integers, let $k_0$ be an algebraically closed field of characteristic $r$, and let $A_0$ be a fake elliptic curve over $k_0$ of level $N$ with $\Lambda$-action (a scheme $A_0.A$ over $\operatorname{Spec} k_0$ with a commutative relative group law, an abelian-scheme property bundle, two-dimensional fibres, and a $\Lambda$-action, together with its level data). Let $\ell$ be a prime distinct from $r$ and let $C_0$ be an extra level-$\ell$ structure on $A_0$: a closed immersion $\mathrm{levK}\colon K \to A_0.A$, finite, flat and locally of finite presentation over the base of fibre rank $\ell^2$, whose points on any base-scheme are closed under the group law and inversion, contain the identity, are killed by $\ell$, are stable under the $\Lambda$-action, meet the level-$N$ structure $A_0.\mathrm{lev}$ only in the identity, and form a group isomorphic to $(\mathbb{Z}/\ell)^2$ on geometric points of residue characteristic $\neq \ell$. The conclusion asserts the existence of a fake elliptic curve $A_{0s}$ over $k_0$ of level $N$ with $\Lambda$-action, and morphisms $as\colon A_0.A \to A_{0s}.A$ and $as'\colon A_{0s}.A \to A_0.A$ over $\operatorname{Spec} k_0$, such that: (i) `IsLevelIsogenyVia` holds for $\ell$, the pair $(A_0,C_0)$, $A_{0s}$, $as$ and $as'$, i.e. both maps are homomorphisms for the group laws on $T$-points, both commute with the $\Lambda$-actions, $as$ followed by $as'$ is the action of $\ell$ on $A_0$ and $as'$ followed by $as$ is the action of $\ell$ on $A_{0s}$ whenever $\ell \in \Lambda$, a $T$-point of $A_0$ is killed by $as$ exactly when it factors through $\mathrm{levK}$, and $as$ carries points factoring through $A_0.\mathrm{lev}$ to points factoring through $A_{0s}.\mathrm{lev}$; (ii) $as$ is an epimorphism of schemes; and (iii) the universal property: for every morphism $\varphi\colon A_0.A \to A_0.A$ over the base which is a homomorphism for the group law on $T$-points for all $T$ and which sends every $T$-point factoring through $\mathrm{levK}$ to the identity, there is a unique morphism $\chi\colon A_{0s}.A \to A_0.A$ over the base with $as$ followed by $\chi$ equal to $\varphi$ and with $\chi$ again a homomorphism for the group laws on $T$-points.
--
--   This is the construction of the quotient of a fake elliptic curve by the finite flat subgroup scheme given by an extra level-$\ell$ structure, together with the dual isogeny realising multiplication by $\ell$ and the universal property characterising maps that factor through the quotient; it is the analogue for quaternionic abelian surfaces of the quotient of an abelian variety by a finite subgroup. It is used in the construction of the $\ell$-isogeny pairs on the Cerednik–Drinfeld side, being cited by `exists_extraLevel_isLevelIsogenyVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLevelIsogenyVia_epi_and_forall_existsUnique_comp_eq
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) (C₀ : A₀.ExtraLevel ℓ) :
    ∃ (A₀s : FakeEllipticCurve Λ N k₀)
      (as : A₀.A ⟶ A₀s.A) (has : as ≫ A₀s.f = A₀.f) (as' : A₀s.A ⟶ A₀.A) (has' : as' ≫ A₀.f = A₀s.f),
      FakeEllipticCurve.IsLevelIsogenyVia ℓ ⟨A₀, C₀⟩ A₀s as has as' has' ∧ Epi as ∧
      ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
          FactorsThrough C₀.levK P → mapPt φ hφ P = A₀.L.one t) →
        ∃! χ : SchemeHomOver A₀s.f A₀.f, as ≫ χ.1 = φ ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀s.f),
        mapPt χ.1 χ.2 (A₀s.L.mul t P Q) = A₀.L.mul t (mapPt χ.1 χ.2 P) (mapPt χ.1 χ.2 Q)) := by sorry
