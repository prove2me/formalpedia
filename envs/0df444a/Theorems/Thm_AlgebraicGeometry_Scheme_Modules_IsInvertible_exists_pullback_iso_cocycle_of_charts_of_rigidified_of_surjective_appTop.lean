-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/729e1aa3-4c19-5519-856e-e0e58df61c63
-- title:
--   Cocycle transition isomorphisms of rigidified invertible modules on charts
-- statement:
--   Let $S$ be a commutative ring, $k$ a natural number and $r : \mathrm{Fin}\,k \to S$ a family whose range generates the unit ideal, and let $B_i$ be commutative $S$-algebras realising the localisation of $S$ away from $r_i$. Let $f : Y \to \operatorname{Spec} S$ be a morphism of schemes, and for each $i$ let $f'_i : A'_i \to \operatorname{Spec} B_i$ and an open immersion $\iota_i : A'_i \to Y$ be given such that the square formed by $\iota_i$, $f'_i$, $f$ and $\operatorname{Spec}$ of the structure map $S \to B_i$ is cartesian, and assume the $\iota_i$ are jointly surjective on points. Assume for each $i$ that the global-sections map of $f'_i$ is surjective, and likewise the global-sections map of the second projection of the base change of $f'_i$ along $\operatorname{Spec}$ of $B_i \to B_i[1/r]$ for every $r \in B_i$. Let $e_i$ be a section of $f'_i$, and assume that for all $i, j$, every $S$-algebra $C$ realising the localisation away from $r_i r_j$ and all $S$-algebra maps $\rho_1 : B_i \to C$, $\rho_2 : B_j \to C$, the composites $\operatorname{Spec}\rho_1$ followed by $e_i$ followed by $\iota_i$ and $\operatorname{Spec}\rho_2$ followed by $e_j$ followed by $\iota_j$ coincide. Let $M_i$ be a module on $A'_i$ which is invertible, in the sense that every point of $A'_i$ has an open neighbourhood $U$ with $(M_i)|_U$ isomorphic to the unit module on $U$; assume each pull-back $e_i^* M_i$ is isomorphic to the unit module on $\operatorname{Spec} B_i$, and that for all $i, j$ and every point $q$ of $A'_i \times_Y A'_j$ there is an open $U \subseteq \operatorname{Spec} S$ containing the image of $q$ under the first projection followed by $\iota_i$ followed by $f$ such that, restricted to the preimage of $U$, the pull-backs of $M_i$ along the first projection and of $M_j$ along the second projection are isomorphic. Then there exist isomorphisms $\varphi_{ij} : p_1^* M_i \cong p_2^* M_j$ on $A'_i \times_Y A'_j$ satisfying the cocycle condition in the following form: for all $i, j, l$, every scheme $T$ and morphisms $\pi_{12}, \pi_{23}, \pi_{13}$ from $T$ to the three double overlaps with $\pi_{12} \circ p_2 = \pi_{23} \circ p_1$, $\pi_{13} \circ p_1 = \pi_{12} \circ p_1$ and $\pi_{13} \circ p_2 = \pi_{23} \circ p_2$ (composites read diagrammatically), the composite of $\pi_{12}^*\varphi_{ij}$ and $\pi_{23}^*\varphi_{jl}$ equals $\pi_{13}^*\varphi_{il}$, both sides being spliced together by the canonical comparison isomorphisms `Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr` for composition of pull-backs and for equal morphisms.
--
--   This is the normalisation step in the descent of a rigidified invertible module from the charts of a scheme over $\operatorname{Spec} S$ to the whole scheme: the rigidifications along the sections $e_i$ pin down the transition isomorphisms on double overlaps uniquely enough for them to satisfy the cocycle condition. It feeds [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop), where the cocycle is glued to a single invertible module on $Y$, as needed for polarisations of abelian schemes constructed chart by chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hsurj : ∀ y : ↥Y, ∃ (i : Fin k) (x : ↥(A' i)), (ι i).base x = y)
    (hΓ : ∀ i, Function.Surjective ((f' i).appTop).hom ∧
      ∀ r : B i, Function.Surjective
        ((pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (B i) (Localization.Away r))))).appTop).hom)
    (e : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A' i) (he : ∀ i, e i ≫ f' i = 𝟙 _)
    (heagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
        (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
        Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ e i ≫ ι i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ e j ≫ ι j)
    (M : ∀ i, (A' i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i))
    (hrig : ∀ i, Nonempty ((Scheme.Modules.pullback (e i)).obj (M i) ≅ SheafOfModules.unit (Spec (CommRingCat.of (B i))).ringCatSheaf))
    (hloc : ∀ (i j : Fin k) (q : ↥(Limits.pullback (ι i) (ι j))), ∃ U : (Spec (CommRingCat.of S)).Opens,
        (pullback.fst (ι i) (ι j) ≫ ι i ≫ f).base q ∈ U ∧
        Nonempty
          ((Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
              ((Scheme.Modules.pullback (pullback.fst (ι i) (ι j))).obj (M i)) ≅
            (Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
              ((Scheme.Modules.pullback (pullback.snd (ι i) (ι j))).obj (M j)))) :
    ∃ φ : ∀ i j : Fin k,
        (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
          (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j),
      ∀ (i j l : Fin k) (T : Scheme.{u})
      (π₁₂ : T ⟶ Limits.pullback (ι i) (ι j)) (π₂₃ : T ⟶ Limits.pullback (ι j) (ι l)) (π₁₃ : T ⟶ Limits.pullback (ι i) (ι l))
      (h₂ : π₁₂ ≫ Limits.pullback.snd (ι i) (ι j) = π₂₃ ≫ Limits.pullback.fst (ι j) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = π₁₂ ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = π₂₃ ≫ Limits.pullback.snd (ι j) (ι l)),

      ((Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₂).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr h₂).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback π₂₃).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l) := by sorry
