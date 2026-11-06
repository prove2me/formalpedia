-- Prove2me | Theorems.Thm_BianchiIX_convex_positiveIntegralClock_target
-- name    : BianchiIX.convex_positiveIntegralClock_target
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:20:22.197344+00:00
-- url     : https://prove2.me/theorems/209d8c94-d904-4aa2-b8c7-c6960155f901
-- title:
--   Convexity of the positive clock image
-- statement:
--   For $a:\mathbb R\to\mathbb R$ and $t_0\in\mathbb R$,
--   define the oriented integral clock
--   $$c_{a,t_0}(t)=\int_{t_0}^t a(u)\,du.$$
--
--   Assume $J\subset\mathbb R$ is open and convex, $t_0\in J$, and $a$ is
--   continuous and strictly positive on $J$. Let $e$ be the open partial
--   homeomorphism constructed from the restriction of $c_{a,t_0}$ to $J$.
--   The target of $e$ is convex.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/IntegralClock.lean#L79-L85

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

theorem BianchiIX.convex_positiveIntegralClock_target {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    Convex ℝ (positiveIntegralClock hJ ho ha ht₀ hpos).target := by sorry
