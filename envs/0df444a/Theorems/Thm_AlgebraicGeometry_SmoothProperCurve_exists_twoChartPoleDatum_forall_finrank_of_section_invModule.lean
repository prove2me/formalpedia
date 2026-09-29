-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_forall_finrank_of_section_invModule
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_forall_finrank_of_section_invModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/94aa782e-6113-54b8-99e5-82bb11c71c17
-- title:
--   Two-chart pole datum of exact order m over a Noetherian base
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c : C \to \operatorname{Spec} R$ be a proper morphism of schemes that is smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is, a morphism $\varepsilon : \operatorname{Spec} R \to C$ with $\varepsilon$ followed by $c$ the identity. Let $m \ge 1$ be a natural number and let $s$ be a morphism from the unit object of the category of modules on $C$ to `(ε.1.ker ^ m).invModule`, the dual (internal hom into the unit) of the module attached to the $m$-th power of the ideal sheaf datum of $\varepsilon$; thus $s$ is a global section of $\mathcal O(m\varepsilon)$. Assume no point in the image of the underlying map of $\varepsilon$ lies in the support of `Scheme.Modules.zeroSchemeIdeal s`, the least ideal sheaf datum whose ideal on each affine open contains the span of the coefficients of $s$. Then there are opens $U, V$ of $C$ with $U \sqcup V = \top$, with $U$ exactly the complement of the image of $\varepsilon$, and sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ such that $U \sqcap V$ equals both $C_{\mathrm{basicOpen}}(f)$ and $C_{\mathrm{basicOpen}}(g)$, the restrictions of $f$ and $g$ to $U \sqcap V$ satisfy $fg = 1$, and: (i) for every field $L$ that is an $R$-algebra, $\Gamma(C,V)$ carrying the $R$-algebra structure induced by $c$, $\dim_L\bigl(L \otimes_R \Gamma(C,V)/(g)\bigr) = m$; (ii) for every field $K$ that is an $R$-algebra, the image of $f$ under the map on sections over $U$ of the first projection of the pullback of $c$ along $\operatorname{Spec} K \to \operatorname{Spec} R$ is transcendental over $K$, for the $K$-algebra structure induced by the second projection; (iii) the same transcendence statement for $g$ over $V$.
--
--   This is the construction, over an arbitrary Noetherian base, of a two-chart pole datum of exact order $m$ from a global section of $\mathcal O(m\varepsilon)$ whose zero scheme avoids the section $\varepsilon$: the classical passage from the linear system $|m\varepsilon|$ on a smooth proper curve to a degree-$m$ map to the projective line, presented as two affine charts glued along $fg = 1$. It feeds the construction of finite map data with $m$ as degree, via [`AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_m_eq_of_forall_invertible_free`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_m_eq_of_forall_invertible_free). Unlike the chart lemma it is built on, the conclusion here does not record that $V$ is the complement of the support of the zero scheme of $s$, and it states the fibre dimension in the base-changed form $\dim_L(L \otimes_R \Gamma(C,V)/(g)) = m$ rather than freeness over a local base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_forall_finrank_of_section_invModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

open MonoidalCategory

theorem AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_forall_finrank_of_section_invModule
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule)
    (hs : ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support) :
    ∃ (U V : C.Opens) (_ : U ⊔ V = ⊤)
      (_ : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
      (f : Γ(C, U)) (g : Γ(C, V))
      (_ : U ⊓ V = C.basicOpen f) (_ : U ⊓ V = C.basicOpen g)
      (_ : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
        (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1),
      (∀ (L : Type u) [Field L] [Algebra R L],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
        Module.finrank L (L ⊗[R] (Γ(C, V) ⧸ Ideal.span {g})) = m) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) := by sorry
