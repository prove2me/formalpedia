-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule
-- name    : AlgebraicGeometry.RelPicard.surjective_of_poincare_pullbackAlong_iso_twistModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/51b1b0e6-069b-5ef7-a859-e2abfe0f93e3
-- title:
--   Surjectivity of the degree-g Abel–Jacobi morphism
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c \colon C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ$-composite equal to the identity, i.e. a section of $c$. Assume `SmoothProperCurve.FiniteMapData` for $(c,\varepsilon)$ exists with invariant $\mathfrak{F}.m$ exceeding any prescribed bound: such data consist of two affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose restrictions to $U \cap V = C_f = C_g$ are mutually inverse, making $\Gamma(C,U)$ and $\Gamma(C,V)$ finite over the respective polynomial algebras over $R$, and such that for every local $R$-algebra $S$ and every $s \in S$ the quotient $S \otimes_R \Gamma(C,U)/(1 \otimes f - s \otimes 1)$ is finite free of rank $m$ over $S$. Let $g \in \mathbb{N}$ be such that for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$, every field extension $L$ of $k$, every `CurveModel` $M$ over $(k,L)$ together with an isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ compatible with the structure morphisms, and all $K_c \in \operatorname{Div}(L/k)$, $g' \in \mathbb{N}$, validity of Riemann–Roch in the form $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$ forces $g' = g$. Let $D$ be a `RelativePic0Designation`, that is a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents the subfunctor of rigidified line bundles on the fibres of $c$ cut out by the fibrewise algebraic-equivalence-to-zero condition `FibrewiseAlgEquivZero`: $h$ provides a Poincaré rigidified line bundle over $D.\mathrm{toBase}$ satisfying that condition, the universal property that every rigidified line bundle over $t \colon T \to \operatorname{Spec} R$ satisfying it is, after pullback of the Poincaré bundle, classified by a unique $T$-morphism to $D.P$ over $\operatorname{Spec} R$, and triviality of the pullback along the zero section. Let $y \colon Y \to \operatorname{Spec} R$ and let $\mathcal{D}$ be a relative effective Cartier divisor of degree $g$ for $c$ over $y$, i.e. an ideal sheaf datum on $C \times_{\operatorname{Spec} R} Y$ whose closed subscheme is finite, flat and locally of finite presentation over $Y$ with all fibre ranks equal to $g$, and assume $\mathcal{D}$ is universal: every relative effective Cartier divisor of degree $g$ over any $t \colon T \to \operatorname{Spec} R$ is pulled back from $\mathcal{D}$ along a unique $T$-morphism to $Y$ over $\operatorname{Spec} R$. Finally let $aj \colon Y \to D.P$ satisfy $aj$ followed by $D.\mathrm{toBase}$ equals $y$, and assume the pullback of the Poincaré bundle along $aj$ has underlying module isomorphic to $\mathcal{D}.\mathrm{twistModule}$, the rigidification along the rigidifying section of the line bundle of $\mathcal{D}$ tensored with the $g$-th power of the ideal of the section $\varepsilon$. Then $aj$ is surjective.
--
--   This is the surjectivity of the Abel–Jacobi morphism $E \mapsto [\mathcal{O}(E - g\varepsilon)]$ from the universal family of relative effective divisors of degree $g$ to a scheme representing the relative $\operatorname{Pic}^0$ of a smooth proper curve with geometrically integral fibres. It feeds the derivation of properness and geometric connectedness of that representing scheme, and so the construction of the Jacobian used in the good-reduction theory of the curves entering the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicCurve MonoidalCategory

theorem AlgebraicGeometry.RelPicard.surjective_of_poincare_pullbackAlong_iso_twistModule
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)} {𝒟 : RelEffCartierDiv c g y} (hU : 𝒟.IsUniversal)
    (aj : Y ⟶ D.P) (haj : aj ≫ D.toBase = y)
    (hclass : Nonempty ((h.poincare.pullbackAlong (⟨aj, haj⟩ : SchemeHomOver y D.toBase)).L ≅ 𝒟.twistModule c ε)) :
    Surjective aj := by sorry
