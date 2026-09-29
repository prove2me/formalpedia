-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/596ccaa0-1fac-5043-9b51-7c717ae17fdf
-- title:
--   Chart quotients for a square-zero thickening realise the stage map
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $c : X \to \operatorname{Spec} R$ a morphism, and $\mathcal V$ a two-affine open cover of $X$, i.e. a pair of opens $U_0, U_1$ that are affine, have affine intersection and satisfy $U_0 \sqcup U_1 = \top$. Let $B$ be an $R$-algebra and $I \subseteq B$ an ideal with $I^2 = 0$. Write $\mathcal V_B$ for the pulled-back cover of $X_B := X \times_{\operatorname{Spec} R} \operatorname{Spec} B$ (its charts are the preimages of $U_0$, $U_1$ under the first projection), $c_B$ for the second projection to $\operatorname{Spec} B$, and $A_0, A_1, A_{01}$ for the associated $B$-algebra chart data of $\mathcal V_B$, namely the sections of $X_B$ over the two charts and over their intersection, together with the two restriction $B$-algebra maps $\rho_0, \rho_1$ into $A_{01}$; write $A_0', A_1', A_{01}'$ for the corresponding data of $\mathcal V_{B/I}$ over $B/I$. Let $\sigma$ be the morphism $X_{B/I} \to X_B$ obtained from the identity of $X$ and $\operatorname{Spec}$ of $B \to B/I$ over $\operatorname{Spec} R$. The assertion is that there exist ideals $J_0 \subseteq A_0$, $J_1 \subseteq A_1$, $J_{01} \subseteq A_{01}$ with $J_0^2 = J_1^2 = J_{01}^2 = 0$ and ring isomorphisms $\varphi_0 : A_0/J_0 \cong A_0'$, $\varphi_1 : A_1/J_1 \cong A_1'$, $\varphi_{01} : A_{01}/J_{01} \cong A_{01}'$ such that $\varphi_{01}$ intertwines $\rho_0$ and $\rho_1$ with $\rho_0'$ and $\rho_1'$ after passing to the quotients, and such that each composite $\varphi_j \circ (\text{quotient map})$ coincides with the `appLE` map of $\sigma$ from the $j$-th chart of $\mathcal V_B$ to the $j$-th chart of $\mathcal V_{B/I}$ (legitimate because the $\sigma$-preimage of the chart of $\mathcal V_B$ is the corresponding chart of $\mathcal V_{B/I}$), for $j = 0, 1$ and for the intersection chart.
--
--   This is the chart-level input for formal smoothness of the relative Picard functor in the style of Bosch–Lütkebohmert–Raynaud, §8.4: it identifies the Čech chart rings of a cover of $X_{B/I}$ with square-zero quotients of those of $X_B$, and pins the identification to the canonical comparison map induced by $B \to B/I$. It is used in the construction of line-bundle lifts along square-zero extensions, [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
    let σst := RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))
    ∃ (J0 : Ideal (𝒱B.cover cB).A0) (J1 : Ideal (𝒱B.cover cB).A1)
      (J01 : Ideal (𝒱B.cover cB).A01),
      J0 ^ 2 = ⊥ ∧ J1 ^ 2 = ⊥ ∧ J01 ^ 2 = ⊥ ∧
      ∃ (φ0 : (𝒱B.cover cB).A0 ⧸ J0 ≃+* (𝒱BI.cover cBI).A0)
        (φ1 : (𝒱B.cover cB).A1 ⧸ J1 ≃+* (𝒱BI.cover cBI).A1)
        (φ01 : (𝒱B.cover cB).A01 ⧸ J01 ≃+* (𝒱BI.cover cBI).A01),
        (∀ a, φ01 ((Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ0 a)) =
          (𝒱BI.cover cBI).ρ0 (φ0 ((Ideal.Quotient.mk J0) a))) ∧
        (∀ a, φ01 ((Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ1 a)) =
          (𝒱BI.cover cBI).ρ1 (φ1 ((Ideal.Quotient.mk J1) a))) ∧
        (∀ a, φ0 ((Ideal.Quotient.mk J0) a) =
          (σst.appLE 𝒱B.U0 𝒱BI.U0
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) ∧
        (∀ a, φ1 ((Ideal.Quotient.mk J1) a) =
          (σst.appLE 𝒱B.U1 𝒱BI.U1
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) ∧
        (∀ a, φ01 ((Ideal.Quotient.mk J01) a) =
          (σst.appLE (𝒱B.U0 ⊓ 𝒱B.U1) (𝒱BI.U0 ⊓ 𝒱BI.U1)
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) := by sorry
