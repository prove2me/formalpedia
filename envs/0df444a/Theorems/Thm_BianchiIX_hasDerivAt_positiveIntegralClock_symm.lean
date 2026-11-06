-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_positiveIntegralClock_symm
-- name    : BianchiIX.hasDerivAt_positiveIntegralClock_symm
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:19:51.213544+00:00
-- url     : https://prove2.me/theorems/426028a3-f818-443f-b51f-9bfd97d74517
-- title:
--   The reciprocal derivative of the inverse integral clock
-- statement:
--   For $a:\mathbb R\to\mathbb R$ and $t_0\in\mathbb R$,
--   define the oriented integral clock
--   $$c_{a,t_0}(t)=\int_{t_0}^t a(u)\,du.$$
--
--   Assume $J\subset\mathbb R$ is open and convex, $t_0\in J$, and $a$ is
--   continuous and strictly positive on $J$. Let $e$ be the open partial
--   homeomorphism constructed from the restriction of $c_{a,t_0}$ to $J$.
--   For every $\tau$ in the target of $e$,
--   $$(e^{-1})'(\tau)=1/a(e^{-1}(\tau)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/IntegralClock.lean#L68-L77

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

theorem BianchiIX.hasDerivAt_positiveIntegralClock_symm {J : Set ℝ} {a : ℝ → ℝ} {t₀ τ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t)
    (hτ : τ ∈ (positiveIntegralClock hJ ho ha ht₀ hpos).target) :
    HasDerivAt (positiveIntegralClock hJ ho ha ht₀ hpos).symm
      (1 / a ((positiveIntegralClock hJ ho ha ht₀ hpos).symm τ)) τ := by sorry
