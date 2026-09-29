-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_section_invModule_pow_ker_disjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/15999e40-f529-5d21-bd77-54f74bc6a49f
-- title:
--   Section of 𝒪(mε) nonvanishing along ε
-- statement:
--   Let $R$ be a commutative local Noetherian ring, let $C$ be a scheme and let $c\colon C \to \operatorname{Spec} R$ be a proper morphism which is smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a morphism over the identity of $\operatorname{Spec} R$, that is, a pair consisting of a morphism $\operatorname{Spec} R \to C$ together with a proof that composing it with $c$ gives the identity of $\operatorname{Spec} R$ — a section of $c$. Then there exist a natural number $m$ with $1 \le m$ and a morphism of $\mathcal O_C$-modules $s$ from the unit object $\mathbf 1$ of $C$'s monoidal category of modules to $(\varepsilon^{\ast}\text{-kernel})^{m}$'s inverse module, i.e. to the dual (internal hom into the unit) of the module attached to the $m$-th power of the ideal sheaf data $\varepsilon.1.\mathrm{ker}$, the module of an ideal sheaf $I$ being the kernel of the unit-to-pushforward-unit map of the closed immersion of the associated closed subscheme; equivalently, $s$ is a global section of $\mathcal O(m\varepsilon)$. This $s$ satisfies: no point $x$ in the range of the underlying continuous map of $\varepsilon$ lies in the support of the ideal sheaf data $\mathrm{zeroSchemeIdeal}\ s$, the infimum of all ideal sheaf data $J$ with the property that on every affine open $U$ the ideal spanned by the coefficients of $s$ over $U$ is contained in $J$'s ideal at $U$.
--
--   This is the existence, on a smooth proper geometrically integral relative curve with a section over a local Noetherian base, of a global section of $\mathcal O(m\varepsilon)$ for some $m \ge 1$ whose zero scheme is disjoint from the image of $\varepsilon$ — concretely, a function with a pole along $\varepsilon$ and no zero there. It is stated without reference to any auxiliary affine cover, and is the input to the construction of a two-affine open cover of $C$ adapted to $\varepsilon$ (with $C$ minus the zero scheme of $s$ and $C$ minus $\varepsilon$ as the two affine pieces) in [`AlgebraicGeometry.SmoothProperCurve.exists_twoAffineOpenCover_of_section`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_twoAffineOpenCover_of_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra
open MonoidalCategory

theorem AlgebraicGeometry.SmoothProperCurve.exists_section_invModule_pow_ker_disjoint
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule),
      ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by sorry
