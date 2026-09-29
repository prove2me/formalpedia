-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/c15e0a7a-47a5-5ffc-ac56-b571537fbb6d
-- title:
--   Gluing rigidified invertible modules along a localisation chart cover
-- statement:
--   Let $S$ be a commutative ring, $k$ a natural number and $r : \mathrm{Fin}\,k \to S$ a family whose span is the unit ideal, and let each $B_i$ be an $S$-algebra realising the localisation of $S$ away from $r_i$. Let $f : Y \to \operatorname{Spec} S$ be a scheme over $S$, and for each $i$ let $f'_i : A'_i \to \operatorname{Spec} B_i$ together with an open immersion $\iota_i : A'_i \to Y$ be given, such that each square formed by $\iota_i$, $f'_i$, $f$ and $\operatorname{Spec}$ of the structure map $S \to B_i$ is cartesian, and such that every point of $Y$ is the image of a point of some $A'_i$. Assume, for each $i$: the ring map on global sections induced by $f'_i$ is surjective, and likewise the global-sections map induced by the second projection of the base change of $f'_i$ along $\operatorname{Spec}$ of $B_i \to B_i[1/r]$ is surjective for every $r \in B_i$. Assume given sections $e_i$ of $f'_i$, agreeing in $Y$ on overlaps in the following sense: whenever $C$ is an $S$-algebra realising the localisation away from $r_i r_j$ and $\rho_1 : B_i \to C$, $\rho_2 : B_j \to C$ are $S$-algebra maps, the composites $\operatorname{Spec} C \to \operatorname{Spec} B_i \to A'_i \to Y$ and $\operatorname{Spec} C \to \operatorname{Spec} B_j \to A'_j \to Y$ coincide. Finally let $M_i$ be modules on $A'_i$ that are invertible in the sense that every point has an open neighbourhood on which the restriction is isomorphic to the unit sheaf of modules, each rigidified along its section, i.e. $e_i^* M_i$ is isomorphic to the unit sheaf on $\operatorname{Spec} B_i$, and assume that for all $i, j$ and every point $q$ of the fibre product $A'_i \times_Y A'_j$ there is an open $U \subseteq \operatorname{Spec} S$ containing the image of $q$ in $\operatorname{Spec} S$ such that the restrictions to the preimage of $U$ of the two pullbacks $p_1^* M_i$ and $p_2^* M_j$ are isomorphic. Then there exists a module $M$ on $Y$, invertible in the same local sense, with $\iota_i^* M \cong M_i$ for every $i$. No group law on the $A'_i$ is assumed; only the sections $e_i$, their agreement on overlaps, and the surjectivity of the global-sections maps are used.
--
--   This is the descent step for rigidified line bundles on a scheme covered by charts pulled back from a standard affine cover $\operatorname{Spec} S[1/r_i]$ of the base: local-on-the-base isomorphism on overlaps plus rigidification along the sections forces the gluing data to satisfy the cocycle condition, so the $M_i$ glue to an invertible module on $Y$. It is used in the construction of pullbacks of polarised abelian schemes and in the comparison of invertible modules that are isomorphic locally on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
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
    ∃ Mg : Y.Modules, Scheme.Modules.IsInvertible Mg ∧ ∀ i, Nonempty ((Scheme.Modules.pullback (ι i)).obj Mg ≅ M i) := by sorry
