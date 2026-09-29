-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber
-- name    : AlgebraicGeometry.Scheme.Hom.eq_of_forall_section_comp_eq_of_dense_of_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/df142e8d-db48-55c8-8835-d98aff2622c8
-- title:
--   Maps from X×_k k[ε] determined by thickened points of a dense open
-- statement:
--   Let $k$ be an algebraically closed field and let $X$, $Y$, $S$ be schemes. Let $f : X \to \operatorname{Spec} k$ be a morphism with $X$ reduced and $f$ locally of finite type, and write $X_\varepsilon$ for the pullback of $f$ along $\operatorname{Spec}$ of the structural map $k \to k[\varepsilon]$ into the dual numbers. Let $F, G : X_\varepsilon \to Y$ be two morphisms, let $i : Y \to S$ be separated, and assume $F$ followed by $i$ equals $G$ followed by $i$. Let $U$ be an open subscheme of $X$ whose underlying set is dense in $X$. Assume that for every $y : \operatorname{Spec} k \to X$ which is a section of $f$ (that is, $y$ followed by $f$ is the identity) and whose image of the closed point of $\operatorname{Spec} k$ lies in $U$, and for every $T : \operatorname{Spec} k[\varepsilon] \to X_\varepsilon$ such that $T$ followed by the first projection equals $\operatorname{Spec}(k \to k[\varepsilon])$ followed by $y$ and $T$ followed by the second projection is the identity of $\operatorname{Spec} k[\varepsilon]$, one has $F \circ T = G \circ T$. Then $F = G$.
--
--   This is a schematic density statement for thickened rational points: on a reduced scheme locally of finite type over an algebraically closed field, the first-order thickenings of the $k$-points of a dense open suffice to separate two $S$-morphisms out of $X \times_k \operatorname{Spec} k[\varepsilon]$, the separatedness of $Y \to S$ making the locus where $F$ and $G$ agree a closed subscheme. It is invoked in the study of polarisations, where equality of two maps on all such tangent-level test objects is checked pointwise in order to place an element in a stabiliser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.eq_of_forall_section_comp_eq_of_dense_of_dualNumber
    (k : Type u) [Field k] [IsAlgClosed k] {X Y S : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ Y)
    (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ (y : Spec (CommRingCat.of k) ⟶ X), y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U →
      ∀ (T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))),
        T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ y →
        T ≫ pullback.snd f _ = 𝟙 _ → T ≫ F = T ≫ G) :
    F = G := by sorry
