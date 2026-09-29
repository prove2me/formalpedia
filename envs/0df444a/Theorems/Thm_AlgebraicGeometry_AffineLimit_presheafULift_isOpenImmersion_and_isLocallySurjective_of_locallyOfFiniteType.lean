-- Prove2me | Theorems.Thm_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.AffineLimit.presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/2a461367-b45f-5be7-bee9-44ec6704b15d
-- title:
--   From finite-type test schemes to all: open charts for locally finitely presented sheaves
-- statement:
--   Let $R$ be a commutative ring and $G$ a presheaf of sets on the opposite of the category of schemes over $\operatorname{Spec} R$, with values in $\mathrm{Type}\,(u+1)$. Write $G^{\mathrm{tot}}$ for `G.overTotal`, the presheaf on schemes sending $T$ to the set of pairs $(t : T \to \operatorname{Spec} R,\ \xi \in G(\mathrm{Over.mk}\,t))$. Assume: $G^{\mathrm{tot}}$ satisfies the sheaf condition for the Zariski topology; `IsLFPSurj`, i.e. for every $R$-algebra $A$ every section of $G$ over $\operatorname{Spec} A$ is pulled back from a section over $\operatorname{Spec} A_0$ for some finitely generated $R$-subalgebra $A_0 \subseteq A$; and `IsLFPInj`, i.e. two sections over such a $\operatorname{Spec} A_0$ with equal pullbacks to $\operatorname{Spec} A$ already agree over $\operatorname{Spec} A_1$ for some finitely generated $A_1$ with $A_0 \le A_1$. Let $X : \iota \to \mathrm{Scheme}$ and let $f_i : \mathrm{uliftYoneda}(X_i) \to G^{\mathrm{tot}}$ be morphisms; let $\xi_i : X_i \to \operatorname{Spec} R$ be the structure morphism component of the section corresponding to $f_i$ under `uliftYonedaEquiv`, and assume each $\xi_i$ satisfies `HomIsLFP`: every $A$-point of $X_i$ over $\operatorname{Spec} R$ factors, compatibly with the structure morphisms, through an $A_0$-point for some finitely generated $R$-subalgebra $A_0 \subseteq A$, and two such $A_0$-points over $\operatorname{Spec} R$ with equal pullbacks to $\operatorname{Spec} A$ agree after passing to some finitely generated $A_1 \supseteq A_0$. Assume finally the hypothesis $H$: for every scheme $T$ and every section $x : \mathrm{uliftYoneda}(T) \to G^{\mathrm{tot}}$ whose structure morphism $T \to \operatorname{Spec} R$ is locally of finite type, there are opens $U_i \subseteq T$ with $\bigsqcup_i U_i = \top$ and morphisms $\varphi_i : U_i \to X_i$ such that $\varphi_i$ followed by $f_i$ equals the inclusion $U_i \hookrightarrow T$ followed by $x$, and such that for every $\psi : T' \to T$ with $\psi$ followed by the structure morphism of $x$ locally of finite type and every $\varphi' : T' \to X_i$ with $\varphi'$ followed by $f_i$ equal to $\psi$ followed by $x$, there is $\chi : T' \to U_i$ with $\chi$ followed by the inclusion equal to $\psi$ and $\chi$ followed by $\varphi_i$ equal to $\varphi'$. Then each $f_i$ lies in `MorphismProperty.presheafULift @IsOpenImmersion`, the relativisation of the open-immersion property along the ULift-Yoneda embedding (so $f_i$ is relatively representable with all base changes along morphisms from representable presheaves given by open immersions of schemes), and the induced morphism $\coprod_i \mathrm{uliftYoneda}(X_i) \to G^{\mathrm{tot}}$ is locally surjective for the Zariski topology.
--
--   This is the standard reduction, for functors locally of finite presentation, of an open-chart criterion tested only on schemes locally of finite type over the base to the same criterion tested on arbitrary schemes, packaged in terms of relative representability by open immersions and local surjectivity for the Zariski topology. It is applied in the construction of open charts for the relative Picard sheaf, where the finite-type case is obtained by explicit means.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType.lean

import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.AffineLimit

theorem AlgebraicGeometry.AffineLimit.presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
    (R : Type u) [CommRing R] (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1))
    (hG : Presieve.IsSheaf Scheme.zariskiTopology G.overTotal)
    (hsurj : IsLFPSurj G) (hinj : IsLFPInj G)
    {ι : Type u} (X : ι → Scheme.{u}) (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ G.overTotal)
    (hX : ∀ i, HomIsLFP (uliftYonedaEquiv (f i)).1)
    (H : ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv x).1 →
      ∃ (U : ι → T.Opens) (φ : ∀ i, (↑(U i) : Scheme.{u}) ⟶ X i),
        (⨆ i, U i) = ⊤ ∧
        ∀ i, uliftYoneda.{u + 1}.map (φ i) ≫ f i = uliftYoneda.{u + 1}.map (U i).ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X i),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑(U i), χ ≫ (U i).ι = ψ ∧ χ ≫ φ i = φ') :
    (∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) := by sorry
