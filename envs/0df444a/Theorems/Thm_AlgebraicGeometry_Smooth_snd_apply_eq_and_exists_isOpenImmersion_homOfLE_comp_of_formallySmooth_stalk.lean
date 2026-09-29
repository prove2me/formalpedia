-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
-- name    : AlgebraicGeometry.Smooth.snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/73852319-24cf-5c7c-a5cf-d62086a59ce5
-- title:
--   Formally smooth chart at a maximal special point is an open immersion
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring property), and let $z\colon Z\to\operatorname{Spec}R$, $f\colon X\to\operatorname{Spec}R$, $g\colon Y\to\operatorname{Spec}R$ be smooth morphisms of schemes with $g$ in addition locally of finite type. Let $\eta$ be a point of the pullback $Z\times_{\operatorname{Spec}R}X$ lying over the closed point of $R$ under the projection to $Z$ followed by $z$, and assume $\eta$ is maximal for specialisation in that fibre: any $y$ of which $\eta$ is a specialisation and which also lies over the closed point equals $\eta$. Let $y_T\in Y$ lie over the closed point of $R$. Let $U_0$ be an open subscheme of $Z\times_{\operatorname{Spec}R}X$ containing $\eta$ and $v\colon U_0\to Z\times_{\operatorname{Spec}R}Y$ a morphism compatible with the projections to $Z$, that is, $v$ followed by the first projection equals the open immersion $U_0\hookrightarrow Z\times_{\operatorname{Spec}R}X$ followed by the first projection. Assume $y_T$ specialises to the image of $\eta$ under $v$ followed by the projection to $Y$; that the stalks $\mathcal O_{U_0,\eta}$ and $\mathcal O_{Z\times_R Y,\,v(\eta)}$ are domains; that, for the algebra structure given by the stalk map of $v$ at $\eta$ followed by localisation, $\operatorname{Frac}(\mathcal O_{U_0,\eta})$ is a fraction ring of $\mathcal O_{Z\times_R Y,\,v(\eta)}$; and that $\mathcal O_{U_0,\eta}$ is formally smooth over $\mathcal O_{Z\times_R Y,\,v(\eta)}$ via that stalk map. Then the image of $\eta$ under $v$ followed by the projection to $Y$ equals $y_T$, and there is an open $U_1$ of $Z\times_{\operatorname{Spec}R}X$ with $\eta\in U_1$ and $U_1\le U_0$ such that the inclusion $U_1\to U_0$ followed by $v$ is an open immersion.
--
--   This is the analytic core of the step in the theory of Néron models in which a formally smooth, birational chart defined near a maximal point of the special fibre is recognised as an open immersion on a smaller neighbourhood, and is simultaneously shown to hit the prescribed special point of the target (Bosch–Lütkebohmert–Raynaud 4.3, Proposition 4). It is used in the construction of translation extensions on neighbourhoods of $\omega$-minimal points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z X Y : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) [Smooth z] [Smooth f] [Smooth g] [LocallyOfFiniteType g]
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (yT : ↑Y) (hyT : g.base yT = IsLocalRing.closedPoint R)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z g) (hv₁ : v ≫ pullback.fst z g = U₀.ι ≫ pullback.fst z f)
    (hgen : yT ⤳ (v ≫ pullback.snd z g).base ⟨η, hηU⟩)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : letI : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : letI : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
    (v ≫ pullback.snd z g).base ⟨η, hηU⟩ = yT ∧
      ∃ (U₁ : (pullback z f).Opens) (_ : η ∈ U₁) (h₁ : U₁ ≤ U₀),
        IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v) := by sorry
