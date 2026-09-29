-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
-- name    : AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/3938aa59-7a8a-55d5-8230-680ac9d2d968
-- title:
--   Fibre Čech dimensions computed on a residue-field affine chart
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $t : T \to \operatorname{Spec} R$ be schemes over $R$, let $A$ be a commutative ring and $j : \operatorname{Spec} A \to T$ an open immersion, and let $\pi_A : C_A \to \operatorname{Spec} A$ together with $g' : C_A \to C \times_{\operatorname{Spec} R} T$ form a pullback square with the second projection $C \times_{\operatorname{Spec} R} T \to T$ and $j$, so that $C_A$ is the part of $C \times_{\operatorname{Spec} R} T$ lying over the open subscheme $\operatorname{Spec} A$. Let $\mathcal V$ be a two-chart affine open cover of $C_A$, that is, opens $U_0, U_1$ with $U_0$, $U_1$ and $U_0 \cap U_1$ affine and $U_0 \cup U_1 = C_A$; let $\mathfrak p$ be a prime of $A$; and let $s : \operatorname{Spec} k \to T$ be a point with values in a field $k$ whose closed point is sent to $j(\mathfrak p)$. Then the fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ admits a two-chart affine open cover $\mathcal W$ such that for every module $M$ on $C \times_{\operatorname{Spec} R} T$ which is invertible, in the sense that every point has an open neighbourhood $U$ over which the restriction of $M$ is isomorphic to the unit sheaf of modules of $U$, the following holds. Write $S$ for the two-chart section datum of $g'^{*}M$ on $\mathcal V$ over $\pi_A$, with Čech differential $d = (-r_0) \oplus r_1 : \Gamma(g'^{*}M, U_0) \times \Gamma(g'^{*}M, U_1) \to \Gamma(g'^{*}M, U_0 \cap U_1)$, and write $S'$ for the two-chart section datum on $\mathcal W$ of the pullback of $M$ to the fibre, taken over the structure map $\operatorname{Spec} k$-ward given by the second projection. Then $\dim_k \ker d' = \dim_{\kappa(\mathfrak p)} \ker(d \otimes_A \kappa(\mathfrak p))$ and $\dim_k \bigl(S'_{01}/\operatorname{im} d'\bigr) = \dim_{\kappa(\mathfrak p)} \bigl((\kappa(\mathfrak p) \otimes_A S_{01})/\operatorname{im}(d \otimes_A \kappa(\mathfrak p))\bigr)$, where $\kappa(\mathfrak p)$ is the residue field of $\mathfrak p$ and $d'$ is the Čech differential of $S'$.
--
--   This is the numerical form of cohomology and base change for a two-chart Čech complex: the dimensions of $\check H^0$ and $\check H^1$ of an invertible module on the fibre at an arbitrary field-valued point $s$ depend only on the prime of $A$ below $s$, and are computed as the kernel and cokernel dimensions of the Čech differential of a single affine chart cover base changed to the residue field. It is used in the relative Picard development to show that Euler characteristics and $\check H^1$-vanishing loci behave well on fibres, notably in the statements that a fibre Euler characteristic is locally constant and that $\check H^1$ of the unit module vanishes on all fibres once $\dim \check H^0 = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

theorem AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T) [IsOpenImmersion j]
    {CA : Scheme.{u}} (πA : CA ⟶ Spec (CommRingCat.of A)) (g' : CA ⟶ pullback c t)
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : PrimeSpectrum A)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (hs : s.base (IsLocalRing.closedPoint k) = j.base 𝔭) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      ∀ (M : (pullback c t).Modules), Scheme.Modules.IsInvertible M →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 =
          Module.finrank 𝔭.asIdeal.ResidueField
            (LinearMap.ker ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
              𝔭.asIdeal.ResidueField)) ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 =
          Module.finrank 𝔭.asIdeal.ResidueField
            ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).M01) ⧸
              LinearMap.range ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
                𝔭.asIdeal.ResidueField)) := by sorry
