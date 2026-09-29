-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/5a701321-2ca2-5430-ac9b-1518c1eb3447
-- title:
--   Base-changed Atkin–Lehner map on lifted K-points of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$ and $r$, commutative rings $R,\mathcal{O}_0,K,C$, a morphism $\bar s:\operatorname{Spec}K\to\operatorname{Spec}R$, and ring maps $c_K:K\to C$, $c_0:\mathcal{O}_0\to C$. Given a scheme $X$ with $\pi_X:X\to\operatorname{Spec}R$ together with a rule $\mathrm{pt}$ attaching, to every commutative ring $S$, every $s:\operatorname{Spec}S\to\operatorname{Spec}R$ and every fake elliptic curve $E$ over $S$ (an abelian scheme datum $E.A\to\operatorname{Spec}S$ with commutative relative group law, two-dimensional fibres, a $\Lambda$-action satisfying the multiplicativity, additivity and trace axioms, and a level structure $E.\mathrm{lev}$), a morphism $\operatorname{Spec}S\to X$ over $s$; the hypothesis `pt_pullback` says that if $\varphi:S\to S'$ satisfies $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$ and $E'$ over $S'$ is a pullback of $E$ along $\varphi$ (a morphism $E'.A\to E.A$ forming a pullback square and compatible with the group laws, the $\Lambda$-actions and the level structures), then $\mathrm{pt}(S',s',E')$ equals $\operatorname{Spec}\varphi$ followed by $\mathrm{pt}(S,s,E)$. Given likewise $f_0:\mathcal{X}_0\to\operatorname{Spec}\mathcal{O}_0$ with a rule $\mathrm{pt}_0$ of points over $\operatorname{Spec}\mathcal{O}_0$, and $\mathrm{ar}:\mathcal{X}_0\to\mathcal{X}_0$ such that whenever $E'$ is an Atkin–Lehner quotient of $E$ at $r$ over $S$ (morphisms $\varphi:E.A\to E'.A$, $\psi:E'.A\to E.A$ over $S$, additive for the group laws, commuting with the $\Lambda$-actions, with $\varphi\psi$ and $\psi\varphi$ the action of $r$ when $r\in\Lambda$, the stated kernel criterion, and compatibility of level structures) one has $\mathrm{pt}_0(S,s,E)$ followed by $\mathrm{ar}$ equal to $\mathrm{pt}_0(S,s,E')$. Assume further an isomorphism $u:X\times_{\operatorname{Spec}R}\operatorname{Spec}C\cong\mathcal{X}_0\times_{\operatorname{Spec}\mathcal{O}_0}\operatorname{Spec}C$ (the first fibre product taken along $\operatorname{Spec}c_K$ followed by $\bar s$) matching, via `hupt`, the lifts of $\mathrm{pt}$ and of $\mathrm{pt}_0$ on all $C$-algebra-valued points, and an endomorphism $a_C$ of $\mathcal{X}_0\times_{\operatorname{Spec}\mathcal{O}_0}\operatorname{Spec}C$ with first projection $a_C$ followed by $\mathrm{pr}_1$ equal to $\mathrm{pr}_1$ followed by $\mathrm{ar}$ and second projection unchanged. Then for fake elliptic curves $E,E'$ over $K$ with $E'$ an Atkin–Lehner quotient of $E$ at $r$, the point $\operatorname{Spec}C\to\mathcal{X}_0\times_{\operatorname{Spec}\mathcal{O}_0}\operatorname{Spec}C$ obtained by lifting $\operatorname{Spec}c_K$ followed by $\mathrm{pt}(K,\bar s,E)$ together with the identity of $\operatorname{Spec}C$, and then applying $u$, composed with $a_C$, equals the point obtained in the same way from $E'$.
--
--   This is the Atkin–Lehner equivariance of the identification of a model $X$ over $R$ with the integral model $\mathcal{X}_0$ after base change to $C$: the endomorphism $a_C$ lifting the Atkin–Lehner map $\mathrm{ar}$ at $r$ sends the lifted $C$-point attached to a fake elliptic curve over $K$ to the lifted $C$-point attached to its Atkin–Lehner quotient. It is used in the Čerednik–Drinfeld comparison to transport Atkin–Lehner data through the completion isomorphisms, being cited by the two germ-comparison lemmas [`CerednikDrinfeld.germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_one_zero_of_two_mul_dvd`](thm.html#CerednikDrinfeld.germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_one_zero_of_two_mul_dvd) and [`CerednikDrinfeld.germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_zero_one_of_two_mul_dvd`](thm.html#CerednikDrinfeld.germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_zero_one_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N r : ℕ)

    (R : Type) [CommRing R] (𝒪₀ : Type) [CommRing 𝒪₀] (K : Type) [CommRing K] (C : Type) [CommRing C]
    (sbar : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (cK : K →+* C) (c₀ : 𝒪₀ →+* C)

    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (ar : 𝒳₀ ⟶ 𝒳₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)

    (u : pullback πX (Spec.map (CommRingCat.ofHom cK) ≫ sbar) ≅ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (hupt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of C)) (E : FakeEllipticCurve Λ N S),
      pullback.lift (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).1 s
          (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).2 ≫ u.hom =
        pullback.lift (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).1 s
          (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).2)

    (aC : pullback f₀ (Spec.map (CommRingCat.ofHom c₀)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (haC₁ : aC ≫ pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) ≫ ar)
    (haC₂ : aC ≫ pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)))

    (E E' : FakeEllipticCurve Λ N K) (hEE' : FakeEllipticCurve.IsAtkinLehnerQuotient r E E') :
    (pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E).1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E).2, Category.id_comp]) ≫ u.hom) ≫ aC =
      pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E').1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E').2, Category.id_comp]) ≫ u.hom := by sorry
