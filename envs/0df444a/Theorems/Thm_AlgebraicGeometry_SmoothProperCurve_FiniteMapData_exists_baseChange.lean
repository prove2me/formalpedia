-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
-- name    : AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/38809b0e-4f84-5008-990d-4a33671308d6
-- title:
--   Finite-map data are stable under base change
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c \colon C \to \operatorname{Spec} R$ a morphism, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$ (an element of `SchemeHomOver (𝟙 _) c`). Let $\mathfrak{F}$ be a finite-map datum for $(c,\varepsilon)$: affine opens $U,V \subseteq C$ with $U \sqcup V = \top$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ and a natural number $m$ such that $U$ is exactly the complement of the set-theoretic image of $\varepsilon$, $U \cap V$ equals both $C_{f \ne 0}$ and $C_{g \ne 0}$, the restrictions of $f$ and $g$ to $U \cap V$ have product $1$, the $R$-algebra maps $\operatorname{aeval} f \colon R[X] \to \Gamma(C,U)$ and $\operatorname{aeval} g \colon R[X] \to \Gamma(C,V)$ (for the $R$-algebra structures induced by $c$) are finite, and for every local $R$-algebra $S$ and every $s \in S$ the quotient $\bigl(S \otimes_R \Gamma(C,U)\bigr)/(1 \otimes f - s \otimes 1)$ is a finite free $S$-module of rank $m$. Let $R'$ be an $R$-algebra. Then there exists a finite-map datum $\mathfrak{F}'$ for the base change $\operatorname{pr}_2 \colon C \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to \operatorname{Spec} R'$ together with the base-changed section `sectionBaseChange R' ε`, whose charts are the preimages $\operatorname{pr}_1^{-1}U$ and $\operatorname{pr}_1^{-1}V$ of those of $\mathfrak{F}$ and whose rank is again $m$, and such that, provided $R$ is local and $R'$ is finite as an $R$-module, the property `LevelSetsGenericallyEtale` for $\mathfrak{F}$ implies it for $\mathfrak{F}'$: the existence of a polynomial $D$ over the base with at least one unit coefficient such that for every local algebra $S$ over the base with local structure map and every $s \in S$ with $D(s)$ a unit, the level-set quotient $\bigl(S \otimes \Gamma(\cdot,\,\text{chart})\bigr)/(1 \otimes f - s \otimes 1)$ is étale over $S$.
--
--   This is the base-change compatibility of the finite-map presentation of a smooth proper relative curve with a section: the two affine charts, their defining sections and the common degree $m$ of the level sets are carried along by the first projection, while the generic-étaleness refinement transports only under the stated restriction to a local base and a module-finite extension. It is used throughout the relative Picard constructions attached to such curves, for instance in producing finite projections and relative effective Cartier divisors from finite-map data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    ∃ 𝔉' : SmoothProperCurve.FiniteMapData (baseChange R c R') (sectionBaseChange R' ε),
      𝔉'.U = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ∧ 𝔉'.V = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V ∧
        𝔉'.m = 𝔉.m ∧
        (IsLocalRing R → Module.Finite R R' → 𝔉.LevelSetsGenericallyEtale → 𝔉'.LevelSetsGenericallyEtale) := by sorry
