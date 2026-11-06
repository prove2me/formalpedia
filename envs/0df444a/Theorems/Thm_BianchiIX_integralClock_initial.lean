-- Prove2me | Theorems.Thm_BianchiIX_integralClock_initial
-- name    : BianchiIX.integralClock_initial
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:17:43.159194+00:00
-- url     : https://prove2.me/theorems/f9fc0b3a-84d0-4233-b2a1-649e2b847875
-- title:
--   The integral clock vanishes at its base time
-- statement:
--   For $a:\mathbb R\to\mathbb R$ and $t_0\in\mathbb R$,
--   define the oriented integral clock
--   $$c_{a,t_0}(t)=\int_{t_0}^t a(u)\,du.$$
--   For every $a,t_0$, $c_{a,t_0}(t_0)=0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/IntegralClock.lean#L14-L15

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

theorem BianchiIX.integralClock_initial (a : ℝ → ℝ) (t₀ : ℝ) : integralClock a t₀ t₀ = 0 := by sorry
