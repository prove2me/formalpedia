-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
-- name    : AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/86ce1806-34a5-5a91-8623-04b037d32d7a
-- title:
--   Čech h⁰ of 𝒪(sum P-sum Q) equals ℓ of the divisor
-- statement:
--   Let $K$ be an algebraically closed field, $X$ an integral scheme with a morphism $x \colon X \to \operatorname{Spec} K$ that is proper and smooth of relative dimension $1$, and let $F$ be a field with a $K$-algebra structure. Let $M$ be a `CurveModel K F`: an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$, a ring isomorphism of $F$ with the function field of $M.C$ compatible with $K$, and a bijection from the closed points of $M.C$ to the places of $F/K$ matching the image of each stalk with the corresponding valuation subring, together with the property that every finite set of points of $M.C$ lies in an affine open. Let $e \colon M.C \cong X$ be an isomorphism with $e.\mathrm{hom}$ followed by $x$ equal to $M.\mathrm{toBase}$. Let $a,b \in \mathbb N$ and let $P \colon \mathrm{Fin}\,a \to \{p \colon \operatorname{Spec} K \to X \mid p \text{ is a section of } x\}$ and $Q \colon \mathrm{Fin}\,b \to \{\dots\}$ be families of $K$-points of $X$ (repetitions allowed), and let $\mathcal V$ be a cover of $X$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Put $N = (\prod_m \mathcal I_{P_m})^{\vee\text{-module}} \otimes (\prod_j \mathcal I_{Q_j})^{\text{module}}$, where for an ideal sheaf $I$ on $X$ the module $I^{\text{module}}$ is the kernel of the unit-to-pushforward-unit map of the associated closed subscheme and $I^{\vee\text{-module}}$ is its dual, and $\mathcal I_p$ denotes the kernel ideal sheaf of the point $p$. The assertion is that, for the two-term complex of $K$-modules $\Gamma(N,U_0) \times \Gamma(N,U_1) \to \Gamma(N, U_0 \sqcap U_1)$ given by the Čech difference, the kernel $H^0$ and the cokernel $H^1$ are finite-dimensional over $K$, and that $\dim_K H^0 = \ell(D)$, the $K$-dimension of the Riemann–Roch space of the divisor $D = \sum_m [v(P_m)] - \sum_j [v(Q_j)] \in (\mathrm{Place}\,K\,F) \to_0 \mathbb Z$, where $v(p)$ is the place of $F/K$ attached by `pointEquivPlace` to the $K$-point $p$ followed by $e^{-1}$ of the model $M$.
--
--   This is the dictionary between the invertible sheaf of a divisor supported on $K$-points of a smooth proper curve and the Riemann–Roch space of the corresponding divisor of its function field, expressed in two-chart Čech cohomology. It is used in the construction of relative Picard data, where charts with vanishing $H^1$ and prescribed $h^0$ are produced for families of line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {F : Type u} [Field F] [Algebra K F] (M : CurveModel K F) (e : M.C ≅ X) (he : e.hom ≫ x = M.toBase)
    {a b : ℕ} (P : Fin a → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _})
    (Q : Fin b → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _}) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 ∧
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H1 ∧
    Module.finrank K (𝒱.sectionsOf x
        ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 =
      ell ((∑ m, Finsupp.single (M.pointEquivPlace ⟨(P m).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2⟩) (1 : ℤ)) -
           ∑ j, Finsupp.single (M.pointEquivPlace ⟨(Q j).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2⟩) (1 : ℤ)) := by sorry
