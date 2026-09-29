-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d13db752-1715-57d3-a8c8-c8511a83f077
-- title:
--   Degree-zero point twists give B-points of the relative Pic⁰
-- statement:
--   Let $R_0$, $R$, $B$ be commutative rings, $\varphi\colon R_0\to R$ and $\rho\colon R\to B$ ring homomorphisms. Let $c\colon X\to\operatorname{Spec} R$ be a scheme over $R$ equipped with a section $\varepsilon$ (a morphism $\operatorname{Spec} R\to X$ with $\varepsilon$ followed by $c$ the identity), and let $D$ consist of a scheme $D.P$ with structure morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec} R$ and a zero section, together with data `hD` exhibiting $D$ as representing, via a Poincaré rigidified line bundle `hD.poincare` on $X\times_R D.P$, the subpresheaf of rigidified line bundles on $X$ satisfying `FibrewiseAlgEquivZero`. Let $y\colon Y\to\operatorname{Spec} R_0$ be proper and smooth of relative dimension $1$, such that for every algebraically closed field $k$ and every morphism $\operatorname{Spec} k\to\operatorname{Spec} R_0$ the base change of $y$ is geometrically integral. Let $f\colon X\to Y$ satisfy $f$ followed by $y$ equals $c$ followed by $\operatorname{Spec}\varphi$, and let $f_B\colon X\times_{\operatorname{Spec} R}\operatorname{Spec} B\to Y\times_{\operatorname{Spec} R_0}\operatorname{Spec} B$ be a morphism compatible with both projections, i.e. $f_B$ followed by the first projection is the first projection followed by $f$, and $f_B$ followed by the second projection is the second projection. Finally let $s_0,\dots,s_{n-1}$ be morphisms $\operatorname{Spec} B\to Y$ over $\operatorname{Spec}(\rho\circ\varphi)$, and let $\mathrm{pos},\mathrm{neg}\colon \{0,\dots,n-1\}\to\mathbb{N}$ satisfy $\sum_i(\mathrm{pos}_i-\mathrm{neg}_i)=0$ in $\mathbb{Z}$. Then there is a morphism $a\colon\operatorname{Spec} B\to D.P$ with $a$ followed by $D.\mathrm{toBase}$ equal to $\operatorname{Spec}\rho$, such that the pull-back of the Poincaré bundle along $a$ is isomorphic, as a module on $X\times_{\operatorname{Spec} R}\operatorname{Spec} B$, to the rigidification along the section $\operatorname{rigSection}$ induced by $\varepsilon$ and the projection to $\operatorname{Spec} B$, namely $L\otimes q^*((\sigma^*L)^\vee)$, of the $f_B$-pull-back of the iterated tensor product $\bigotimes_i (I_i^{\mathrm{pos}_i})^\vee\otimes I_i^{\mathrm{neg}_i}$ formed by a right fold over $\{0,\dots,n-1\}$ starting from the tensor unit, where $I_i$ is the ideal sheaf of the relative effective Cartier divisor of degree $1$ cut out by the graph of $s_i$ in $Y\times_{\operatorname{Spec} R_0}\operatorname{Spec} B$. Only existence of $a$ is asserted, not uniqueness.
--
--   This is the statement that a divisor supported at $B$-valued points of a smooth proper curve with geometrically integral geometric fibres, of total degree zero, pulled back along a morphism of curves and rigidified along the chosen section, is algebraically equivalent to zero on fibres and hence classified by a $B$-valued point of the scheme representing the rigidified relative $\mathrm{Pic}^0$. It supplies the points of the Jacobian attached to explicit degree-zero combinations of cusps and other sections, and is used in the computation identifying such combinations on the model of $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_pullback_foldr_ofPoint_of_sum_eq_zero
    {R₀ R B : Type u} [CommRing R₀] [CommRing R] [CommRing B] (φ : R₀ →+* R) (ρ : R →+* B)
    {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D : RelativePic0Designation R c} (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R₀)) [IsProper y] [SmoothOfRelativeDimension 1 y]
    (hgi : ∀ (k : Type u) [Field k] [IsAlgClosed k] (u : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀)),
      GeometricallyIntegral (pullback.snd y u))
    (f : X ⟶ Y) (hf : f ≫ y = c ≫ Spec.map (CommRingCat.ofHom φ))
    (fB : pullback c (Spec.map (CommRingCat.ofHom ρ)) ⟶ pullback y (Spec.map (CommRingCat.ofHom (ρ.comp φ))))
    (hfB₁ : fB ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f)
    (hfB₂ : fB ≫ pullback.snd _ _ = pullback.snd _ _)
    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ.comp φ))) y)
    (pos neg : Fin n → ℕ) (hdeg : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0) :
    ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong a).L ≅
        Scheme.Modules.rigidify (rigSection c (Spec.map (CommRingCat.ofHom ρ)) ε) (pullback.snd c (Spec.map (CommRingCat.ofHom ρ)))
          ((Scheme.Modules.pullback fB).obj
            ((List.finRange n).foldr
              (fun i N => ((RelEffCartierDiv.ofPoint y (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
                ((RelEffCartierDiv.ofPoint y (s i).1 (s i).2).I ^ (neg i)).module ⊗ N)
              (𝟙_ (pullback y (Spec.map (CommRingCat.ofHom (ρ.comp φ)))).Modules)))) := by sorry
