-- Prove2me | Theorems.Thm_ClassicalGradIsWeakGrad
-- name    : ClassicalGradIsWeakGrad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:15.468653+00:00
-- url     : https://prove2.me/theorems/da8504b3-9d77-4f1c-9cc4-66982c2db412
-- title:
--   Classical Grad Is Weak Grad: Classical Grad Is Weak Grad
-- statement:
--   On an open set, the CLASSICAL gradient of a `C^1` function is its DISTRIBUTIONAL gradient:
--   for every test function `φ` supported in `U`,
--   `∫_U w • gradient φ = - ∫_U φ • gradient w`.
--
--   This is the integration-by-parts identity that every weak formulation in the paper rests on,
--   and it is exactly the `weakGrad` field of `IsLinearDivSol` and of `IsPHarm` once the weak
--   gradient is taken to be the classical one.  Stated for a merely `C^1` function on an open set,
--   which is all any consumer needs and all the proof uses.
--
--   The proof multiplies `w` by the test function and applies `TestFunctionGradientIntegral` to the
--   product.  The product is `C^1` on all of the plane rather than only on `U` because `tsupport φ`
--   is a closed set contained in `U`, so `U` and the complement of `tsupport φ` are two open sets
--   covering the plane on each of which the product is `C^1` -- on the second it vanishes
--   identically.  That gluing is why the hypothesis `tsupport φ ⊆ U` cannot be weakened to
--   `Function.support φ ⊆ U`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/ClassicalGradIsWeakGrad.lean#L19-L116
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/ClassicalGradIsWeakGrad.lean#L19-L116

import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_ClassicalGradIsWeakGrad
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false

theorem ClassicalGradIsWeakGrad (U : Set Plane) (hU : IsOpen U) (w : Plane → ℝ)
    (hw : ContDiffOn ℝ 1 w U) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, w x • gradient φ x = - ∫ x in U, φ x • gradient w x := by sorry
