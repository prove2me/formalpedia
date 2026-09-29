-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/3a941b3b-4fa5-5c04-96e1-f18012d700b8
-- title:
--   Base change of the two-chart Čech complex of Ω¹
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\mathcal V$ a `TwoAffineOpenCover` of $X$, i.e. two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine; let $c\colon X\to\operatorname{Spec} R$ be a morphism and $A$ a commutative $R$-algebra. Via $c$ the rings $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\sqcap U_1)$ of $\mathcal V.\mathrm{cover}\ c$ are $R$-algebras with restriction maps $\rho_0,\rho_1$, and $\mathcal V.\mathrm{pullback}\ c\ A$ is the two-affine-open cover of $X\times_{\operatorname{Spec} R}\operatorname{Spec} A$ by the preimages of $U_0,U_1$ under the first projection, viewed over $A$ through the second projection. The assertion is the existence of $A$-linear isomorphisms $e_0,e_1,e_{01}$ from $A\otimes_R\Omega_{A_i/R}$ ($i=0,1,01$) onto the corresponding modules $\Omega_{\bullet/A}$ of the pulled-back cover, of an $A$-linear isomorphism $e_{H^0}$ from the kernel of the base change along $A$ of the Čech differential $\delta=(-\rho_{0*})\mathbin{\mathrm{coprod}}\rho_{1*}\colon \Omega_{A_0/R}\times\Omega_{A_1/R}\to\Omega_{A_{01}/R}$ onto the kernel of the corresponding differential for the pulled-back cover over $A$, and of an $A$-linear isomorphism $e_{H^1}$ from $(A\otimes_R\Omega_{A_{01}/R})/\operatorname{im}(\delta\otimes A)$ onto the cokernel of that differential, subject to: $e_i(a\otimes\omega)=a\cdot f^{*}\omega$ where $f^{*}$ denotes the semilinear maps `kaehlerMap0`, `kaehlerMap1`, `kaehlerMap01` attached to the `HomOver` given by the first projection; $e_{H^0}(x)$ has components $e_0$ and $e_1$ applied to the two components of $x$ under the canonical identification $A\otimes_R(M_0\times M_1)\cong (A\otimes_R M_0)\times(A\otimes_R M_1)$; and $e_{H^1}$ sends the class of $y$ to the class of $e_{01}(y)$.
--
--   This is the affine base-change statement for Kähler differentials, packaged so that the two-chart Čech complex computing $\check H^0$ and $\check H^1$ of $\Omega^1_{X/R}$ on $\mathcal V$ base changes to the corresponding complex for $X_A$ on the pulled-back cover. It is the differentials analogue of the structure-sheaf statement [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf), and is used in comparing $\check H^0(\Omega^1)$ with $\check H^1(\mathcal O)$ and in the base-change behaviour of Laurent charts and residues for curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections.lean

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Mathlib.LinearAlgebra.TensorProduct.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : (A ⊗[R] Ω[(𝒱.cover c).A0⁄R]) ≃ₗ[A]
          Ω[((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A0⁄A])
      (e1 : (A ⊗[R] Ω[(𝒱.cover c).A1⁄R]) ≃ₗ[A]
          Ω[((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A1⁄A])
      (e01 : (A ⊗[R] Ω[(𝒱.cover c).A01⁄R]) ≃ₗ[A]
          Ω[((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01⁄A])
      (eH0 : LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange A) ≃ₗ[A]
          ((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0)
      (eH1 : ((A ⊗[R] Ω[(𝒱.cover c).A01⁄R]) ⧸ LinearMap.range ((𝒱.kaehlerSections c).cechDiff.baseChange A))
          ≃ₗ[A] ((𝒱.pullback c A).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
      (∀ a ω, e0 (a ⊗ₜ[R] ω) = a • (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).kaehlerMap0 ω) ∧
      (∀ a ω, e1 (a ⊗ₜ[R] ω) = a • (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).kaehlerMap1 ω) ∧
      (∀ a ω, e01 (a ⊗ₜ[R] ω) = a • (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).kaehlerMap01 ω) ∧
      (∀ x, ((eH0 x : _ × _)) = (e0 (TensorProduct.prodRight R A A _ _ x.1).1,
          e1 (TensorProduct.prodRight R A A _ _ x.1).2)) ∧
      (∀ y, eH1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 y)) := by sorry
