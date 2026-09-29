-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units
-- name    : AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.smul_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/249e2cd8-6366-51e8-82a2-1d298ea2e5ca
-- title:
--   Rescaling all gluing units by a global unit preserves node-unit modules
-- statement:
--   Let $\kappa$ be a field and let $x\colon X\to\operatorname{Spec}\kappa$, $c_1\colon C_1\to\operatorname{Spec}\kappa$, $c_2\colon C_2\to\operatorname{Spec}\kappa$ be schemes over $\kappa$. Let $i_1$, $i_2$ be morphisms over $\operatorname{Spec}\kappa$, that is elements of `SchemeHomOver c₁ x` and `SchemeHomOver c₂ x`: morphisms $C_1\to X$, $C_2\to X$ whose composites with $x$ are $c_1$, $c_2$. Let $\iota$ be an index type and let $p_1,p_2$ assign to each $j\in\iota$ sections of $c_1$, resp. $c_2$ (elements of `SchemeHomOver (𝟙 (Spec (.of κ))) c₁`, resp. of the analogue for $c_2$), i.e. $\kappa$-points of $C_1$ and of $C_2$. Let $h\colon T\to\operatorname{Spec}\kappa$ be a base, let $u\colon\iota\to\Gamma(T,\top)^\times$ be a family of global units on $T$, and let $M$ be a sheaf of modules on the base change $X_T=$ `pullback x h`. Assume `IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M`: there exist morphisms $j_1\colon M\to (\mathrm{curveChange}\,i_1)_*\mathcal O_{C_{1,T}}$ and $j_2\colon M\to (\mathrm{curveChange}\,i_2)_*\mathcal O_{C_{2,T}}$ (pushforwards of the unit sheaves of modules on `pullback c₁ h`, `pullback c₂ h`) such that for every open $W$ of $X_T$ the map $m\mapsto (j_1.\mathrm{app}\,W\,m,\;j_2.\mathrm{app}\,W\,m)$ is injective with image exactly the set of pairs $(f,g)$ satisfying, for every $j\in\iota$, the node condition that the restriction of $f$ along `nodeSectionFst p₁ h j` to the node locus equals the image of $u_j$ in $\Gamma(T,\top)$ times the restriction of $g$ along `nodeSectionSnd p₂ h j`. Then for every global unit $c\in\Gamma(T,\top)^\times$ the same $M$ also satisfies `IsNodeUnitModule` for the rescaled family $j\mapsto c\cdot u_j$.
--
--   The node-unit modules here are the structure sheaves of line bundles on a curve obtained by gluing $C_1$ and $C_2$ at the prescribed pairs of rational points, described by their gluing units at the nodes; the statement says that the diagonal action of $\Gamma(T,\mathcal O_T)^\times$ on the family of gluing units does not change the module, so that only the classes of $(u_j)_j$ modulo the diagonal matter. It is used in the identification of the relevant kernel of the restriction map on relative Picard groups with a split torus of character lattice $\mathbb{Z}^{\iota}/\mathbb{Z}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra AlgebraicGeometry.TwoGluedCurves

theorem AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.smul_units
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M : (pullback x h).Modules}
    (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) (c : Γ(T, ⊤)ˣ) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h (fun j => c * u j) M := by sorry
