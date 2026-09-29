-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph
-- name    : AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/9c6bbe0e-edd8-5511-84c8-67f878457728
-- title:
--   Extending a generic-fibre morphism across a graph-closure point
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$ (realised as an $R$-algebra that is a fraction ring of $R$), and let $g\colon G\to\operatorname{Spec}R$ and $h\colon H\to\operatorname{Spec}R$ be morphisms of schemes with $G$ integral, $g$ locally of finite type, and $h$ separated, locally of finite type and quasi-compact. Let $\eta\in G$ be a point lying over the closed point of $\operatorname{Spec}R$ such that every point of $G$ over the closed point lies in the closure of $\eta$ (i.e. $\eta$ specialises to it), and assume the local ring $\mathcal O_{G,\eta}$ is a discrete valuation ring. Let $\varphi_K\colon G\times_R K\to H\times_R K$ be a morphism compatible with the two projections to $\operatorname{Spec}K$, and let $\Gamma$ be the scheme-theoretic image of the graph morphism $(\mathrm{pr}_1,\varphi_K\,\mathrm{pr}_1)\colon G\times_R K\to G\times_R H$. Assume $\Gamma$ has a point $\gamma$ whose image under $\Gamma\hookrightarrow G\times_R H\to G$ is $\eta$. Then there are an open subscheme $V\subseteq G$ and a morphism $v\colon V\to H$ with $v$ followed by $h$ equal to the inclusion $V\hookrightarrow G$ followed by $g$, such that $V$ contains every point of $G$ not lying over the closed point of $\operatorname{Spec}R$ as well as $\eta$, and such that the image of $G\times_R K\to G$ is contained in $V$, the induced morphism $G\times_R K\to V$ followed by $v$ being equal to $\varphi_K$ followed by the projection $H\times_R K\to H$.
--
--   This is the extension step in the Weil-style criterion for prolonging a morphism given on the generic fibre over a discrete valuation ring: a point of the schematic closure of the graph lying over the generic point $\eta$ of the special fibre forces $\varphi_K$ to extend over an open set containing the generic fibre and $\eta$. It is used in [`AlgebraicGeometry.Scheme.exists_opens_extension_of_pointwise_extension_dense`](thm.html#AlgebraicGeometry.Scheme.exists_opens_extension_of_pointwise_extension_dense) and [`AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_mem_closure_range`](thm.html#AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_mem_closure_range), where such extensions are glued or turned into sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
    [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (η : G) (hη : g.base η = IsLocalRing.closedPoint R)
    (hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
    [IsDiscreteValuationRing (G.presheaf.stalk η)]
    (φK : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
      pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hφK : φK ≫ pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (γ : ↥((pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).image))
    (hγ : ((pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).imageι ≫
          pullback.fst g h).base γ = η) :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧
      (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      η ∈ V ∧
      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆
          Set.range V.ι.base,
        IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
          φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by sorry
