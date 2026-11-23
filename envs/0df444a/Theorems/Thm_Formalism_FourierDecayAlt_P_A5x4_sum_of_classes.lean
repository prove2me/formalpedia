-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_sum_of_classes
-- name    : Formalism.FourierDecayAlt.P.A5x4.sum_of_classes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:10.875831+00:00
-- url     : https://prove2.me/theorems/b11da81f-188c-4c13-a5f4-88707f853159
-- title:
--   A5x4: sum of classes
-- statement:
--   The A5x4 construction uses the sum of classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L394-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L394-L418

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4

theorem Formalism.FourierDecayAlt.P.A5x4.sum_of_classes {T Q : Type} [Fintype T] [Fintype Q] [DecidableEq Q] (f : T → Q)
    (μ : Q → ℝ) (c : T → ℂ) :
    ∑ i, ∑ j, c i * conj (c j) * (if f i = f j then (μ (f i) : ℂ) else 0) =
      ((∑ κ, μ κ * Complex.normSq (∑ i, if f i = κ then c i else 0) : ℝ) : ℂ) := by sorry
