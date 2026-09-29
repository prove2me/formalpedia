-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/cde4f65a-03f9-5cdf-a2f3-4af4b29f711c
-- title:
--   Overlap base-change isomorphisms for lifted chart modules
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme with a structure morphism $c : C \to \operatorname{Spec} R$, and $\mathcal V$ a two-affine open cover of $C$, that is, affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine. Let $B$ be an $R$-algebra and $I \subseteq B$ an ideal, write $C_B$ and $C_{B/I}$ for the fibre products of $c$ with $\operatorname{Spec} B \to \operatorname{Spec} R$ and with $\operatorname{Spec}(B/I) \to \operatorname{Spec} R$, and let $c_B$, $c_{B/I}$ be their second projections; the cover $\mathcal V$ pulls back to two-affine open covers of $C_B$ and of $C_{B/I}$, with chart rings $A_0^B, A_1^B, A_{01}^B$ (the sections of $C_B$ over the preimages of $U_0$, $U_1$, $U_0 \cap U_1$, as $R$-algebras) and restriction $R$-algebra maps $\rho_0, \rho_1$ into $A_{01}^B$, and similarly over $B/I$. Let $M$ be a module over $C_{B/I}$ which is invertible, i.e. every point has an open neighbourhood $U$ on which the pullback of $M$ along $U \hookrightarrow C_{B/I}$ is isomorphic to the unit sheaf of modules; write $P_0, P_1, M_{01}$ for its modules of sections over the preimages of $U_0$, $U_1$, $U_0 \cap U_1$, with restriction maps $r_0, r_1$ satisfying $r_j(a \cdot m) = \rho_j(a) \cdot r_j(m)$. Let $J_0 \subseteq A_0^B$, $J_1 \subseteq A_1^B$, $J_{01} \subseteq A_{01}^B$ be ideals (no square-zero or other condition is imposed on them), and let $\varphi_0 : A_0^B/J_0 \cong A_0^{B/I}$, $\varphi_1 : A_1^B/J_1 \cong A_1^{B/I}$, $\varphi_{01} : A_{01}^B/J_{01} \cong A_{01}^{B/I}$ be ring isomorphisms compatible with restriction, in the sense that $\varphi_{01}(\overline{\rho_0 a}) = \rho_0(\varphi_0(\bar a))$ for all $a \in A_0^B$ and $\varphi_{01}(\overline{\rho_1 a}) = \rho_1(\varphi_1(\bar a))$ for all $a \in A_1^B$. Finally let $P_0'$ be a projective $A_0^B$-module and $P_1'$ a projective $A_1^B$-module, and, viewing $P_0$ as an $A_0^B/J_0$-module through $\varphi_0$ and $P_1$ as an $A_1^B/J_1$-module through $\varphi_1$, let $\mathrm{iso}_0 : (A_0^B/J_0) \otimes_{A_0^B} P_0' \cong P_0$ and $\mathrm{iso}_1 : (A_1^B/J_1) \otimes_{A_1^B} P_1' \cong P_1$ be linear equivalences. Then, regarding $A_{01}^B$ as an $A_0^B$-algebra via $\rho_0$ and as an $A_1^B$-algebra via $\rho_1$, and $M_{01}$ as an $A_{01}^B/J_{01}$-module through $\varphi_{01}$, there exist $(A_{01}^B/J_{01})$-linear isomorphisms $\mathrm{iso}_{01,0} : (A_{01}^B/J_{01}) \otimes_{A_{01}^B} (A_{01}^B \otimes_{A_0^B} P_0') \cong M_{01}$ and $\mathrm{iso}_{01,1} : (A_{01}^B/J_{01}) \otimes_{A_{01}^B} (A_{01}^B \otimes_{A_1^B} P_1') \cong M_{01}$ such that $\mathrm{iso}_{01,0}(1 \otimes (1 \otimes p)) = r_0(\mathrm{iso}_0(1 \otimes p))$ for all $p \in P_0'$ and $\mathrm{iso}_{01,1}(1 \otimes (1 \otimes p)) = r_1(\mathrm{iso}_1(1 \otimes p))$ for all $p \in P_1'$.
--
--   This is the Čech-theoretic comparison step in the deformation theory of line bundles on a scheme covered by two affine opens: the base changes to the overlap chart of two chart-wise lifts are identified, after reduction, with the overlap sections of the given invertible module, compatibly with the two restriction maps on generators. It is used in the construction of lifts of rigidified line bundles along a square-zero extension, [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover), and rests on the overlap base-change isomorphisms for invertible modules, [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (J0 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A0)
    (J1 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A1)
    (J01 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A01) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
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
      (P0' : Type u) [AddCommGroup P0'] [Module A0B P0'] [Module.Projective A0B P0']
      (P1' : Type u) [AddCommGroup P1'] [Module A1B P1'] [Module.Projective A1B P1'],
      letI : Module (A0B ⧸ J0) P0 := Module.compHom P0 φ0.toRingHom
      letI : Module (A1B ⧸ J1) P1 := Module.compHom P1 φ1.toRingHom
      ∀ (iso0 : (A0B ⧸ J0) ⊗[A0B] P0' ≃ₗ[A0B ⧸ J0] P0)
        (iso1 : (A1B ⧸ J1) ⊗[A1B] P1' ≃ₗ[A1B ⧸ J1] P1),
      letI : Algebra A0B A01B := (𝒱B.cover cB).ρ0.toRingHom.toAlgebra
      letI : Algebra A1B A01B := (𝒱B.cover cB).ρ1.toRingHom.toAlgebra
      letI : Module (A01B ⧸ J01) (𝒱BI.sectionsOf cBI M).M01 := Module.compHom _ φ01.toRingHom
      ∃ (iso01₀ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A0B] P0') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01)
        (iso01₁ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A1B] P1') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01),
        (∀ p : P0', iso01₀ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A0B] p)) =
              (𝒱BI.sectionsOf cBI M).r0 (iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p))) ∧
        (∀ p : P1', iso01₁ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A1B] p)) =
              (𝒱BI.sectionsOf cBI M).r1 (iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p))) := by sorry
