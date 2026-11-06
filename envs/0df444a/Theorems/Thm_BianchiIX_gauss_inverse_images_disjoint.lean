-- Prove2me | Theorems.Thm_BianchiIX_gauss_inverse_images_disjoint
-- name    : BianchiIX.gauss_inverse_images_disjoint
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:40:28.621336+00:00
-- url     : https://prove2.me/theorems/b6e6f0fa-8777-4bb7-a727-123d5d91a094
-- title:
--   Disjoint images of the Gauss inverse branches
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $T(0)=0$.
--   For $b\geq1$, write $g_b(x)=1/(b+x)$, using the total reciprocal $0^{-1}=0$.
--   For any $A\subset(0,1)$, the sets $g_{j+1}(A)$,
--   $j\geq0$, are pairwise disjoint.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInvariant.lean#L41-L54

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open Set MeasureTheory
open scoped ENNReal
open BianchiIX

theorem BianchiIX.gauss_inverse_images_disjoint {A : Set ℝ} (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    Pairwise (fun i j : ℕ => Disjoint
      (gaussInv ((i : ℝ) + 1) '' A) (gaussInv ((j : ℝ) + 1) '' A)) := by sorry
