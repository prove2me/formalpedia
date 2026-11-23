-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_psd_of_rel
-- name    : Formalism.FourierDecayAlt.P.A5x4.psd_of_rel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:20.157046+00:00
-- url     : https://prove2.me/theorems/17774155-f152-4428-bc26-8d2f6180d0f4
-- title:
--   A5x4: psd of rel
-- statement:
--   The A5x4 construction uses the psd of rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L420-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L420-L441

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

theorem Formalism.FourierDecayAlt.P.A5x4.psd_of_rel {T : Type} [Fintype T] (r : Setoid T) (N : T → T → ℕ)
    (h0 : ∀ i j, ¬ r i j → N i j = 0) (h1 : ∀ i j k, r i j → r i k → N i j = N k k)
    (c : T → ℂ) :
    (∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ)).re := by sorry
