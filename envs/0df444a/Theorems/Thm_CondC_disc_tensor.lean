-- Prove2me | Theorems.Thm_CondC_disc_tensor
-- name    : CondC.disc_tensor
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T15:50:08.696043+00:00
-- url     : https://prove2.me/theorems/8c3c63e7-3a6d-4ce5-a1da-9944186fabf1
-- title:
--   The liquid tensor product of disc algebras (Theorem 4.1)
-- statement:
--   Theorem 4.1 of the paper: for each 0 < p at most 1, the space O(D) is p-liquid and flat for the p-liquid tensor product, and the k-fold p-liquid tensor product of O(D) identifies with O(D^k), the polydisc algebra. The milestone isolates the universal-property content: given a bilinear combination of two polydisc-algebra spaces into a target T whose coefficients factor as the products of the coefficients of its two arguments - the coefficient-side expression of O(D) tensor O(D) = O(D^2) - the target T is p-liquid, and every liquid bilinear map factors uniquely through the combination. The liquid bilinear maps are those carrying designated null sequences to designated null sequences in each variable.
--
--   **Formalization Note** The liquid tensor product is an infinity-categorical construction in the paper and is replaced here by this universal property over the liquid interface; the flatness half of Theorem 4.1 is not part of the statement and is carried in prose.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (May 2026 version), Lecture IV (Theorem 4.1).

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

namespace CondC

/-!  Milestone 2: the liquid tensor product of disc algebras. If the
coefficients of a bilinear combination conv factor as the products of the
coefficients of its two arguments, then the target carries a p-liquid
structure, and every liquid bilinear map factors uniquely through conv.
This is the universal-property content of Theorem 4.1: the k-fold liquid
tensor product of the disc algebra is the polydisc algebra.  -/
theorem disc_tensor : ∀ (p r : ℝ), 0 < p → p ≤ 1 → 0 < r →
    ∀ (V W T U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      [AddCommGroup T] [Module ℂ T] [AddCommGroup U] [Module ℂ U],
      ∀ (dV : DiscAlgebraData2 r V) (dW : DiscAlgebraData2 r W)
        (dT : DiscAlgebraData2 r T),
      ∀ (lV : PLiquidStructure p V) (lW : PLiquidStructure p W)
        (lU : PLiquidStructure p U),
      ∀ (conv : V →ₗ[ℂ] W →ₗ[ℂ] T),
      (∀ (v : V) (w : W) (i j : ℕ),
        dT.coeffs (conv v w) (i, j) = dV.coeffs v i * dW.coeffs w j) →
      IsPLiquid p T ∧
      ∀ b : V →ₗ[ℂ] W →ₗ[ℂ] U, LiquidBilinear p V W U lV lW lU b →
        ∃! L : T →ₗ[ℂ] U, ∀ (v : V) (w : W), L (conv v w) = b v w := by sorry

end CondC
