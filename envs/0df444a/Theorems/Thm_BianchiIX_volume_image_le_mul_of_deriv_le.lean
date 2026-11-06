-- Prove2me | Theorems.Thm_BianchiIX_volume_image_le_mul_of_deriv_le
-- name    : BianchiIX.volume_image_le_mul_of_deriv_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:25:15.568548+00:00
-- url     : https://prove2.me/theorems/e57b3dbd-c05d-4579-8dd6-a85245161c86
-- title:
--   Image measure comparison from a derivative bound
-- statement:
--   Let $A\subset\mathbb R$ be Borel measurable. Suppose $F,G:\mathbb R\to\mathbb R$
--   are injective on $A$ and have derivatives $D_F(x),D_G(x)$ at every $x\in A$.
--   If $C\geq0$ and $|D_F(x)|\leq C|D_G(x)|$ on $A$, then
--   $$\lambda(F(A))\leq C\lambda(G(A)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussTransport.lean#L20-L35

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

theorem BianchiIX.volume_image_le_mul_of_deriv_le {F F' G G' : ℝ → ℝ} {A : Set ℝ} {C : ℝ}
    (hA : MeasurableSet A) (hF : ∀ x ∈ A, HasDerivAt F (F' x) x)
    (hG : ∀ x ∈ A, HasDerivAt G (G' x) x) (hFinj : InjOn F A) (hGinj : InjOn G A)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ A, |F' x| ≤ C * |G' x|) :
    volume (F '' A) ≤ ENNReal.ofReal C * volume (G '' A) := by sorry
