-- Prove2me | Theorems.Thm_BianchiIX_volume_image_eq_lintegral_abs_deriv
-- name    : BianchiIX.volume_image_eq_lintegral_abs_deriv
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:21:12.546602+00:00
-- url     : https://prove2.me/theorems/27baf1ef-9865-4612-ac67-980418c41551
-- title:
--   One-dimensional image measure formula
-- statement:
--   Let $A\subset\mathbb R$ be Borel measurable and let $F:\mathbb R\to\mathbb R$
--   be injective on $A$. Suppose $F$ has derivative $D(x)$ at every $x\in A$.
--   Writing $\lambda$ for Lebesgue measure,
--   $$\lambda(F(A))=\int_A |D(x)|\,d\lambda(x),$$
--   where the integral is the nonnegative extended integral.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussTransport.lean#L14-L18

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace BianchiIX
end BianchiIX

open BianchiIX
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal

theorem BianchiIX.volume_image_eq_lintegral_abs_deriv {F F' : ℝ → ℝ} {A : Set ℝ}
    (hA : MeasurableSet A) (hF : ∀ x ∈ A, HasDerivAt F (F' x) x) (hinj : InjOn F A) :
    volume (F '' A) = ∫⁻ x in A, ENNReal.ofReal |F' x| := by sorry
