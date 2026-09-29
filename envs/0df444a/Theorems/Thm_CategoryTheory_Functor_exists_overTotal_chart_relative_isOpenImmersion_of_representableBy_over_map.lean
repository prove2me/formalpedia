-- Prove2me | Theorems.Thm_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
-- name    : CategoryTheory.Functor.exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/282a902f-4a13-5d7c-ad88-768a04b482e3
-- title:
--   Open chart of the total presheaf from representability over U
-- statement:
--   Let $j\colon U \to S$ be an open immersion of schemes, let $G$ be a presheaf of types on the category of $S$-schemes, and write $G^{\mathrm{tot}}$ for the presheaf `G.overTotal` on schemes whose value at $T$ is the set of pairs $\langle t, \xi\rangle$ with $t\colon T \to S$ and $\xi \in G(\mathrm{op}\,(T \xrightarrow{t} S))$, functorially in $T$. Let $p\colon Y \to U$ be a morphism and let $e$ exhibit the object $p$ of $\mathrm{Over}\,U$ as representing the presheaf obtained from $G$ by restriction along $\mathrm{Over.map}\,j$, i.e. along $(T \to U) \mapsto (T \to U \to S)$. Then there is a morphism $\varphi$ from the (universe-lifted) functor of points of $Y$ to $G^{\mathrm{tot}}$ such that: (i) for every scheme $T$ and every $y\colon T \to Y$, the induced $T$-point of $G^{\mathrm{tot}}$ is the pair consisting of the structure morphism $(y \circ p) \circ j\colon T \to S$ together with the element of $G$ corresponding under $e$ to $y$ viewed as a morphism $(T \xrightarrow{y\circ p} U) \to (Y \xrightarrow{p} U)$ of $U$-schemes; (ii) $\varphi$ satisfies `MorphismProperty.relative` for the lifted Yoneda embedding and the property `IsOpenImmersion`, that is, $\varphi$ is relatively representable by open immersions of schemes; and (iii) for every scheme $T$, every $T$-point $x$ of $G^{\mathrm{tot}}$ whose first component $t\colon T \to S$ has topological image contained in the image of $j$ factors as $\psi$ followed by $\varphi$ for some $\psi\colon T \to Y$.
--
--   This is the chart form of the statement that representability of a Zariski sheaf is local on the base: a representing object for the restriction of $G$ to $U$-schemes yields an open chart of the total presheaf $G^{\mathrm{tot}}$, covering exactly those points whose structure morphism lands in $U$. It is the generic input to the representability results for the relative Picard cut, being used in [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway) and in [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations), where finitely many such charts coming from local representing objects are glued.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map.lean

import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

theorem CategoryTheory.Functor.exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
    {S U : Scheme.{u}} (j : U ⟶ S) [IsOpenImmersion j]
    (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    {Y : Scheme.{u}} (p : Y ⟶ U) (e : ((Over.map j).op ⋙ G).RepresentableBy (Over.mk p)) :
    ∃ φ : uliftYoneda.{u + 1}.obj Y ⟶ G.overTotal,
      (∀ {T : Scheme.{u}} (y : T ⟶ Y),
        uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ φ) =
          ⟨(y ≫ p) ≫ j, e.homEquiv (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p)⟩) ∧
      MorphismProperty.relative uliftYoneda.{u + 1} @IsOpenImmersion φ ∧
      ∀ {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
        Set.range ((uliftYonedaEquiv x).1).base ⊆ Set.range j.base →
        ∃ ψ : T ⟶ Y, uliftYoneda.{u + 1}.map ψ ≫ φ = x := by sorry
