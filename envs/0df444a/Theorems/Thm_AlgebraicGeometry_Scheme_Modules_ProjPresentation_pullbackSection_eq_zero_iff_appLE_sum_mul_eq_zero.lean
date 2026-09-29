-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/29b79f28-8cbf-5029-83b7-f34f8e71c04e
-- title:
--   Vanishing of a pulled-back section in a chart of a Proj presentation
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ an $\mathcal O_X$-module, $N$ a natural number, and let $\mathfrak P$ be a `ProjPresentation` of $M$ over $f$ of rank $N$: global sections $\sigma_0,\dots,\sigma_N \in \Gamma(M,\top)$, a morphism $\varphi = \mathfrak P.\mathrm{toProj} : X \to \operatorname{Proj}$ of the ring of polynomials in $N+1$ variables over $R$ with its standard grading, such that $\varphi$ followed by the structure map $\operatorname{Proj} \to \operatorname{Spec} R$ is $f$, such that on every open $V$ contained in $U_i := \varphi^{-1}D_+(X_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective, and such that $\sigma_j|_{U_i} = \varphi^\sharp(X_j/X_i)\,\sigma_i|_{U_i}$ for all $i,j$. Let $s : \mathcal O_X \to M$ be a morphism from the unit module, $c : \{0,\dots,N\} \to R$, and assume $s$ sends the global unit section $1$ to $\sum_j f^\sharp(c_j)\,\sigma_j$, where $f^\sharp$ is the map on global sections induced by $f$ composed with the inverse of the iso $R \cong \Gamma(\operatorname{Spec} R,\top)$. Let $B$ be a commutative ring, $t : \operatorname{Spec} B \to X$ a morphism, and $i$ an index with $\top \le t^{-1}U_i$, i.e. $t$ factors through the chart $U_i$. Then the pulled-back section $t^*s : \mathcal O_{\operatorname{Spec} B} \to t^*M$, obtained from $s$ by applying the pullback functor along $t$ and the canonical identification of $t^*\mathcal O_X$ with $\mathcal O_{\operatorname{Spec} B}$, is zero if and only if the image under $t^\sharp : \Gamma(X,U_i) \to \Gamma(\operatorname{Spec} B,\top) = B$ of $\sum_j f^\sharp(c_j)|_{U_i} \cdot \varphi^\sharp\bigl(X_j/X_i\bigr)$ vanishes, where $X_j/X_i$ denotes the degree-zero element $\mathrm{ratio}\,R\,N\,i\,j$ of the homogeneous localisation away from $X_i$, viewed as a section over $D_+(X_i)$.
--
--   This is the standard computation of the value of a global section at a $B$-valued point, read in one of the coordinate charts of a presentation of $M$ by $N+1$ generating sections together with the resulting morphism to projective space: on $U_i$ the section $s$ equals $\bigl(\sum_j f^\sharp(c_j)\varphi^\sharp(X_j/X_i)\bigr)\sigma_i$, and $\sigma_i$ remains a frame after pullback. It is the arithmetic input for the rigidity results that recover $\varphi \circ t$, and hence $t$ itself, from knowledge of which pulled-back sections vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : Scheme.Modules.ProjPresentation M f N)
    (s : 𝟙_ X.Modules ⟶ M) (c : Fin (N + 1) → R)
    (hs : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      ∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c j))) • 𝔓.σ j)
    {B : Type u} [CommRing B] (t : Spec (CommRingCat.of B) ⟶ X) (i : Fin (N + 1))
    (ht : ⊤ ≤ t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) :
    Scheme.Modules.pullbackSection t s = 0 ↔
      (t.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ⊤ ht).hom
        (∑ j, (f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
                le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c j)) *
          (𝔓.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))).hom
            (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) = 0 := by sorry
