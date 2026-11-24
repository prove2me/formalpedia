-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_hasFDerivAt_integral_pIter
-- name    : Formalism.IndefR.Tow.SobPf.Avg.hasFDerivAt_integral_pIter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:14.586139+00:00
-- url     : https://prove2.me/theorems/21206744-906e-4b89-901f-477db6e542f0
-- title:
--   Avg: has FDeriv At integral p Iter
-- statement:
--   The Avg construction uses the has FDeriv At integral p Iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L46-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L46-L75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.SobPf Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem Formalism.IndefR.Tow.SobPf.Avg.hasFDerivAt_integral_pIter {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμK : μ Kᶜ = 0) {Φ : (Fin m → ℝ) → X → E}
    (hΦ : ∀ k ∈ K, ContDiff ℝ ∞ fun t => Φ t k)
    (hc : ∀ j : ℕ, ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K))
    (j : ℕ) (t₀ : Fin m → ℝ) :
    HasFDerivAt (fun t => ∫ k, pIter Φ j t k ∂μ)
      (∫ k, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E (pIter Φ (j + 1) t₀ k) ∂μ)
      t₀ := by sorry
