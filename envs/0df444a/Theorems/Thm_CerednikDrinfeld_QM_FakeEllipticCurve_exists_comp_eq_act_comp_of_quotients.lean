-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_act_comp_of_quotients
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/011d7495-cd1f-5f67-b050-cca9c646b342
-- title:
--   Descending m through two point-quotients of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and an algebraically closed field $k$. Let $E$ be a `FakeEllipticCurve Λ N k`, that is a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$ carrying a commutative relative group law $E.L$ on $T$-points, the abelian-scheme properties (smooth, proper, connected fibres, a group law), two-dimensional fibres, and an action $x \mapsto E.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms over the base satisfying the compatibilities recorded in that structure. For $j=1,2$ one is given a set $H_j$ of $k$-points of $E$ (sections of $E.f$ over $\mathrm{id}_{\operatorname{Spec} k}$), a fake elliptic curve $C_j$, a morphism $p_j : E.A \to C_j.A$ over $\operatorname{Spec} k$, a scheme $K_j$ and a morphism $\kappa_j : K_j \to E.A$, subject to: $p_j$ is a homomorphism for the group laws on $T$-points (composition with $p_j$ turns $E.L.\mathrm{mul}$ into $C_j.L.\mathrm{mul}$); $p_j$ is $\Lambda$-equivariant, $E.\mathrm{act}\,x$ followed by $p_j$ equalling $p_j$ followed by $C_j.\mathrm{act}\,x$; $p_j$ is finite, flat and surjective, and surjective on $k$-points; $\kappa_j$ is a closed immersion with $K_j$ reduced and $\kappa_j$ followed by $E.f$ finite; the $k$-points of $E$ that factor through $\kappa_j$ are exactly those in $H_j$; and, for every test scheme $T$ with structure morphism $t$, a $T$-point $Q$ of $E$ satisfies $p_j \circ Q = C_j.L.\mathrm{one}\,t$ precisely when $Q$ factors through $\kappa_j$. Let $m \in \Lambda$ be such that composing any point of $H_1$ with $E.\mathrm{act}\,m$ gives a point of $H_2$. Then there is a morphism $\theta : C_1.A \to C_2.A$ over $\operatorname{Spec} k$ with $p_1$ followed by $\theta$ equal to $E.\mathrm{act}\,m$ followed by $p_2$; $\theta$ is a homomorphism for the group laws on $T$-points; $\theta$ is the unique morphism over the base with that intertwining property; and for every $x \in \Lambda$ whose action commutes with that of $m$ and which carries $H_1$ into itself, $C_1.\mathrm{act}\,x$ followed by $\theta$ equals $\theta$ followed by $C_2.\mathrm{act}\,x$.
--
--   This is the descent of an endomorphism through quotient isogenies: $E.\mathrm{act}\,m$ composed with $p_2$ kills the kernel of $p_1$, hence factors uniquely through $p_1$, and the factorisation is again a homomorphism, equivariant for those elements of $\Lambda$ that commute with $m$ and stabilise $H_1$. It is used in the construction of extra level structures and of Atkin–Lehner quotients of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_act_comp_of_quotients.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (H₁ : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (C₁ : FakeEllipticCurve Λ N k) (p₁ : E.A ⟶ C₁.A) (hp₁ : p₁ ≫ C₁.f = E.f) (K₁ : Scheme.{0}) (κ₁ : K₁ ⟶ E.A)
    (hC₁ :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt p₁ hp₁ (E.L.mul t P Q) = C₁.L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p₁ = p₁ ≫ C₁.act x) ∧
      IsFinite p₁ ∧ Flat p₁ ∧ Surjective p₁ ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) C₁.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, mapPt p₁ hp₁ P = R) ∧
      IsClosedImmersion κ₁ ∧ IsReduced K₁ ∧ IsFinite (κ₁ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough κ₁ P ↔ P ∈ H₁) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E.f),
        mapPt p₁ hp₁ Q = C₁.L.one t ↔ FactorsThrough κ₁ Q))
    (H₂ : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (C₂ : FakeEllipticCurve Λ N k) (p₂ : E.A ⟶ C₂.A) (hp₂ : p₂ ≫ C₂.f = E.f) (K₂ : Scheme.{0}) (κ₂ : K₂ ⟶ E.A)
    (hC₂ :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt p₂ hp₂ (E.L.mul t P Q) = C₂.L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p₂ = p₂ ≫ C₂.act x) ∧
      IsFinite p₂ ∧ Flat p₂ ∧ Surjective p₂ ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) C₂.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, mapPt p₂ hp₂ P = R) ∧
      IsClosedImmersion κ₂ ∧ IsReduced K₂ ∧ IsFinite (κ₂ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough κ₂ P ↔ P ∈ H₂) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E.f),
        mapPt p₂ hp₂ Q = C₂.L.one t ↔ FactorsThrough κ₂ Q))
    (m : ↥Λ) (hm : ∀ P, P ∈ H₁ → pushPt (E.act m) (E.act_over m) P ∈ H₂) :
    ∃ (θ : C₁.A ⟶ C₂.A) (hθ : θ ≫ C₂.f = C₁.f),
      p₁ ≫ θ = E.act m ≫ p₂ ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t C₁.f),
        mapPt θ hθ (C₁.L.mul t P Q) = C₂.L.mul t (mapPt θ hθ P) (mapPt θ hθ Q)) ∧
      (∀ θ' : C₁.A ⟶ C₂.A, θ' ≫ C₂.f = C₁.f → p₁ ≫ θ' = E.act m ≫ p₂ → θ' = θ) ∧
      (∀ x : ↥Λ, E.act m ≫ E.act x = E.act x ≫ E.act m →
        (∀ P, P ∈ H₁ → pushPt (E.act x) (E.act_over x) P ∈ H₁) →
          C₁.act x ≫ θ = θ ≫ C₂.act x) := by sorry
