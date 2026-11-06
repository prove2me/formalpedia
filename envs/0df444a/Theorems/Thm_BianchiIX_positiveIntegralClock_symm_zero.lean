-- Prove2me | Theorems.Thm_BianchiIX_positiveIntegralClock_symm_zero
-- name    : BianchiIX.positiveIntegralClock_symm_zero
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:27:55.27331+00:00
-- url     : https://prove2.me/theorems/e2b4be03-a156-4baf-a10d-38660fe502cf
-- title:
--   The inverse clock at zero
-- statement:
--   For $a:\mathbb R\to\mathbb R$ and $t_0\in\mathbb R$,
--   define the oriented integral clock
--   $$c_{a,t_0}(t)=\int_{t_0}^t a(u)\,du.$$
--
--   Assume $J\subset\mathbb R$ is open and convex, $t_0\in J$, and $a$ is
--   continuous and strictly positive on $J$. Let $e$ be the open partial
--   homeomorphism constructed from the restriction of $c_{a,t_0}$ to $J$.
--   One has $e^{-1}(0)=t_0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/IntegralClock.lean#L87-L94

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

theorem BianchiIX.positiveIntegralClock_symm_zero {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    (positiveIntegralClock hJ ho ha ht₀ hpos).symm 0 = t₀ := by sorry
