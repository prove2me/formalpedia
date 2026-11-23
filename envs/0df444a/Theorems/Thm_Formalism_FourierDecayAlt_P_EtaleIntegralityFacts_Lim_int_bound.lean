-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_int_bound
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.int_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:45.207797+00:00
-- url     : https://prove2.me/theorems/1e462fa3-82b6-40d6-b751-d5be1b714154
-- title:
--   Lim: int bound
-- statement:
--   The Lim construction uses the int bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1949-L1973
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1949-L1973

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.int_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f g : α → V) (maj : α → ℝ) (S : Set α) (hS : MeasurableSet S)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (hmaj : Integrable maj μ)
    (hmaj0 : ∀ y, 0 ≤ maj y) {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hfb : ∀ y, ‖f y‖ ≤ B * maj y)
    (hgb : ∀ y, ‖g y‖ ≤ B * maj y) (hin : ∀ y, y ∉ S → ‖f y - g y‖ ≤ B * τ * maj y) :
    ‖∫ y, f y ∂μ - ∫ y, g y ∂μ‖ ≤ B * τ * ∫ y, maj y ∂μ + 2 * B * ∫ y in S, maj y ∂μ := by sorry
