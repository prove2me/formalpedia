-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/606d748d-638d-5a91-8f11-f345391d52a5
-- title:
--   Pullback of a glued lift along B → B/I recovers M
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ with a morphism $c : C \to \operatorname{Spec} R$, and a two-affine open cover $\mathcal V$ of $C$ (affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine). Let $B$ be an $R$-algebra, $I \subseteq B$ an ideal, and $\iota$ a morphism $\operatorname{Spec}(B/I) \to \operatorname{Spec} B$ over $\operatorname{Spec} R$ with $\iota$ equal to $\operatorname{Spec}$ of the quotient map. Let $M$ be a sheaf of modules on $P_{B/I} := C \times_{\operatorname{Spec} R} \operatorname{Spec}(B/I)$ which is invertible in the sense that every point has an open neighbourhood $V$ with the restriction of $M$ to $V$ isomorphic to the unit sheaf of modules. Write $\mathcal V_B, \mathcal V_{B/I}$ for the base-changed covers (preimages of $U_0, U_1$ under the first projection), $A_0^B, A_1^B, A_{01}^B$ for the section rings of $\mathcal V_B$ over $U_0, U_1, U_0 \sqcap U_1$ with their restriction $R$-algebra maps $\rho_0, \rho_1$, and $P_0 = \Gamma(M, U_0^{B/I})$, $P_1 = \Gamma(M, U_1^{B/I})$, $M_{01} = \Gamma(M, U_0^{B/I} \sqcap U_1^{B/I})$; let $\sigma^{\mathrm{st}} : P_{B/I} \to C \times_{\operatorname{Spec} R} \operatorname{Spec} B$ be the morphism induced by $B \to B/I$. Given ideals $J_0 \subseteq A_0^B$, $J_1 \subseteq A_1^B$, $J_{01} \subseteq A_{01}^B$, ring isomorphisms $\varphi_0 : A_0^B/J_0 \cong A_0^{B/I}$, $\varphi_1 : A_1^B/J_1 \cong A_1^{B/I}$, $\varphi_{01} : A_{01}^B/J_{01} \cong A_{01}^{B/I}$ that intertwine the restriction maps $\rho_0, \rho_1$ on the two sides and each of which, composed with the quotient map, equals the map on sections induced by $\sigma^{\mathrm{st}}$ on the relevant opens; further given $A_0^B$- and $A_1^B$-modules $P_0'$, $P_1'$, isomorphisms $\mathrm{iso}_0 : (A_0^B/J_0) \otimes_{A_0^B} P_0' \cong P_0$ and $\mathrm{iso}_1 : (A_1^B/J_1) \otimes_{A_1^B} P_1' \cong P_1$ (semilinear via $\varphi_0, \varphi_1$), an $A_{01}^B$-linear isomorphism $\sigma' : A_{01}^B \otimes_{A_0^B} P_0' \cong A_{01}^B \otimes_{A_1^B} P_1'$, and an isomorphism $\mathrm{iso}_{01} : (A_{01}^B/J_{01}) \otimes_{A_{01}^B} (A_{01}^B \otimes_{A_0^B} P_0') \cong M_{01}$ with $\mathrm{iso}_{01}(1 \otimes 1 \otimes p) = r_0(\mathrm{iso}_0(1 \otimes p))$ for $p \in P_0'$ and $\mathrm{iso}_{01}(1 \otimes \sigma'^{-1}(1 \otimes p)) = r_1(\mathrm{iso}_1(1 \otimes p))$ for $p \in P_1'$, where $r_0, r_1$ are the restriction maps of $M$; finally given an invertible sheaf of modules $L'$ on $C \times_{\operatorname{Spec} R} \operatorname{Spec} B$ together with linear isomorphisms $e_0' : \Gamma(L', U_0^B) \cong P_0'$, $e_1' : \Gamma(L', U_1^B) \cong P_1'$, $e_{01}' : \Gamma(L', U_0^B \sqcap U_1^B) \cong A_{01}^B \otimes_{A_0^B} P_0'$ satisfying $e_{01}'(r_0 m) = 1 \otimes e_0' m$ and $\sigma'(e_{01}'(r_1 m)) = 1 \otimes e_1' m$: then the pullback of $L'$ along the morphism $P_{B/I} \to C \times_{\operatorname{Spec} R} \operatorname{Spec} B$ induced by $\iota$ is isomorphic to $M$ (the conclusion asserts nonemptiness of the set of such isomorphisms). No hypothesis of the form $I^2 = 0$ is assumed.
--
--   This is the final comparison step in the construction, over a two-affine open cover, of a lift of an invertible sheaf along a thickening $\operatorname{Spec}(B/I) \hookrightarrow \operatorname{Spec} B$: it says that a sheaf $L'$ glued from chart data $(P_0', P_1', \sigma')$ whose reduction is matched with $M$ by the isomorphisms $\varphi_j$, $\mathrm{iso}_j$, $\mathrm{iso}_{01}$ does indeed restrict to $M$. It feeds the formal-smoothness statement [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover) for the relative Picard functor, and is proved from the Čech-style recognition lemma `nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible` together with the base-change descriptions of the section rings and section modules of the pulled-back cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)
    (ι : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hι : ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (J0 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A0)
    (J1 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A1)
    (J01 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A01) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
    let σst := RelPicard.baseChangeSnd c
      (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))
    let A0B := (𝒱B.cover cB).A0
    let A1B := (𝒱B.cover cB).A1
    let A01B := (𝒱B.cover cB).A01
    let P0 := (𝒱BI.sectionsOf cBI M).M0
    let P1 := (𝒱BI.sectionsOf cBI M).M1
    ∀ (φ0 : A0B ⧸ J0 ≃+* (𝒱BI.cover cBI).A0)
      (φ1 : A1B ⧸ J1 ≃+* (𝒱BI.cover cBI).A1)
      (φ01 : A01B ⧸ J01 ≃+* (𝒱BI.cover cBI).A01)
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ0 a)) =
                (𝒱BI.cover cBI).ρ0 (φ0 (Ideal.Quotient.mk J0 a)))
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ1 a)) =
                (𝒱BI.cover cBI).ρ1 (φ1 (Ideal.Quotient.mk J1 a)))
      (_ : ∀ a, φ0 (Ideal.Quotient.mk J0 a) =
          (σst.appLE 𝒱B.U0 𝒱BI.U0
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a)
      (_ : ∀ a, φ1 (Ideal.Quotient.mk J1 a) =
          (σst.appLE 𝒱B.U1 𝒱BI.U1
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a)
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 a) =
          (σst.appLE (𝒱B.U0 ⊓ 𝒱B.U1) (𝒱BI.U0 ⊓ 𝒱BI.U1)
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a)
      (P0' : Type u) [AddCommGroup P0'] [Module A0B P0']
      (P1' : Type u) [AddCommGroup P1'] [Module A1B P1'],
      letI : Module (A0B ⧸ J0) P0 := Module.compHom P0 φ0.toRingHom
      letI : Module (A1B ⧸ J1) P1 := Module.compHom P1 φ1.toRingHom
      ∀ (iso0 : (A0B ⧸ J0) ⊗[A0B] P0' ≃ₗ[A0B ⧸ J0] P0)
        (iso1 : (A1B ⧸ J1) ⊗[A1B] P1' ≃ₗ[A1B ⧸ J1] P1),
      letI : Algebra A0B A01B := (𝒱B.cover cB).ρ0.toRingHom.toAlgebra
      letI : Algebra A1B A01B := (𝒱B.cover cB).ρ1.toRingHom.toAlgebra
      letI : Module (A01B ⧸ J01) (𝒱BI.sectionsOf cBI M).M01 := Module.compHom _ φ01.toRingHom
      ∀ (σ' : A01B ⊗[A0B] P0' ≃ₗ[A01B] A01B ⊗[A1B] P1')
        (iso01 : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A0B] P0') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01)
        (_ : ∀ (p : P0'), iso01 ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A0B] p)) =
              (𝒱BI.sectionsOf cBI M).r0 (iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p)))
        (_ : ∀ (p : P1'), iso01 ((1 : A01B ⧸ J01) ⊗ₜ[A01B] (σ'.symm ((1 : A01B) ⊗ₜ[A1B] p))) =
              (𝒱BI.sectionsOf cBI M).r1 (iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p)))
        (L' : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R B)).Modules)
        (_ : Scheme.Modules.IsInvertible L')
        (e0' : (𝒱B.sectionsOf cB L').M0 ≃ₗ[A0B] P0')
        (e1' : (𝒱B.sectionsOf cB L').M1 ≃ₗ[A1B] P1')
        (e01' : (𝒱B.sectionsOf cB L').M01 ≃ₗ[A01B] A01B ⊗[A0B] P0')
        (_ : ∀ m, e01' ((𝒱B.sectionsOf cB L').r0 m) = (1 : A01B) ⊗ₜ[A0B] e0' m)
        (_ : ∀ m, σ' (e01' ((𝒱B.sectionsOf cB L').r1 m)) = (1 : A01B) ⊗ₜ[A1B] e1' m),
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ι)).obj L' ≅ M) := by sorry
