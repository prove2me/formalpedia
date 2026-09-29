-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion
-- name    : AlgebraicGeometry.exists_isPullback_glue_of_isPullback_of_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3a765dab-c332-5c79-b1d2-a4f90bd17e08
-- title:
--   Gluing two models of open pieces along a common open model
-- statement:
--   Let $R$ be a commutative ring and $A$ an $R$-algebra, and write $\iota \colon \operatorname{Spec} A \to \operatorname{Spec} R$ for the morphism induced by $R \to A$. Over $\operatorname{Spec} R$ let $u_0 \colon U_0 \to \operatorname{Spec} R$ and $v_0 \colon V_0 \to \operatorname{Spec} R$ be quasi-compact, quasi-separated and locally of finite presentation, and let $a \colon W_0 \to U_0$, $b \colon W_0 \to V_0$ be open immersions with $a \gg u_0 = b \gg v_0$ (so $W_0$ maps to $\operatorname{Spec} R$ unambiguously), this composite being assumed quasi-compact. Let $g \colon X \to \operatorname{Spec} A$ be given, together with open immersions $j_U \colon U \to X$ and $j_V \colon V \to X$ whose images cover the underlying space of $X$, and morphisms $k_U \colon W \to U$, $k_V \colon W \to V$ exhibiting $W$ as the fibre product $U \times_X V$. Assume further morphisms $\pi_U \colon U \to U_0$, $\pi_V \colon V \to V_0$, $\pi_W \colon W \to W_0$ such that the squares $(\pi_U, j_U \gg g; u_0, \iota)$ and $(\pi_V, j_V \gg g; v_0, \iota)$ are cartesian, i.e. $U = U_0 \times_{\operatorname{Spec} R} \operatorname{Spec} A$ and $V = V_0 \times_{\operatorname{Spec} R} \operatorname{Spec} A$, and such that $(k_U, \pi_W; \pi_U, a)$ and $(k_V, \pi_W; \pi_V, b)$ are cartesian, i.e. $W = U \times_{U_0} W_0 = V \times_{V_0} W_0$. Then there exist a scheme $X_0$, a morphism $f_0 \colon X_0 \to \operatorname{Spec} R$, a morphism $\pi \colon X \to X_0$ and open immersions $i_U \colon U_0 \to X_0$, $i_V \colon V_0 \to X_0$ such that $i_U \gg f_0 = u_0$, $i_V \gg f_0 = v_0$, $a \gg i_U = b \gg i_V$, the images of $i_U$ and $i_V$ cover $X_0$, the square $(a, b; i_U, i_V)$ is cartesian (so $W_0 = U_0 \times_{X_0} V_0$), $\pi_U \gg i_U = j_U \gg \pi$ and $\pi_V \gg i_V = j_V \gg \pi$, the morphism $f_0$ is quasi-compact, quasi-separated and locally of finite presentation, and the square $(\pi, g; f_0, \iota)$ is cartesian, i.e. $X = X_0 \times_{\operatorname{Spec} R} \operatorname{Spec} A$ compatibly with the charts.
--
--   This is the gluing step in the descent of a scheme locally of finite presentation over $A$ to a model over a subring $R$: given models over $R$ of two open pieces of $X$ and of a model of their intersection, it produces a model of the union. It is used in the proof of [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation), where an induction over a finite affine cover glues the model of the first pieces to that of the next one along a model of the overlap.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isPullback_glue_of_isPullback_of_isOpenImmersion
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {U₀ V₀ W₀ : Scheme.{u}} (u₀ : U₀ ⟶ Spec (CommRingCat.of R)) (v₀ : V₀ ⟶ Spec (CommRingCat.of R))
    (a : W₀ ⟶ U₀) (b : W₀ ⟶ V₀) [IsOpenImmersion a] [IsOpenImmersion b] (hab : a ≫ u₀ = b ≫ v₀)
    [QuasiCompact u₀] [QuasiSeparated u₀] [LocallyOfFinitePresentation u₀]
    [QuasiCompact v₀] [QuasiSeparated v₀] [LocallyOfFinitePresentation v₀] [QuasiCompact (a ≫ u₀)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A))
    {U V W : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcov : Set.range jU.base ∪ Set.range jV.base = Set.univ)
    (kU : W ⟶ U) (kV : W ⟶ V) (hW : IsPullback kU kV jU jV)
    (πU : U ⟶ U₀) (hU : IsPullback πU (jU ≫ g) u₀ (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (πV : V ⟶ V₀) (hV : IsPullback πV (jV ≫ g) v₀ (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (πW : W ⟶ W₀) (hWU : IsPullback kU πW πU a) (hWV : IsPullback kV πW πV b) :
    ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of R)) (π : X ⟶ X₀) (iU : U₀ ⟶ X₀) (iV : V₀ ⟶ X₀),
      IsOpenImmersion iU ∧ IsOpenImmersion iV ∧ iU ≫ f₀ = u₀ ∧ iV ≫ f₀ = v₀ ∧ a ≫ iU = b ≫ iV ∧
      Set.range iU.base ∪ Set.range iV.base = Set.univ ∧ IsPullback a b iU iV ∧
      πU ≫ iU = jU ≫ π ∧ πV ≫ iV = jV ≫ π ∧
      QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧ LocallyOfFinitePresentation f₀ ∧
      IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by sorry
