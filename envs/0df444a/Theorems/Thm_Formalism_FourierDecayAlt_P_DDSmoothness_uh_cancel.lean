-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_cancel
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.uh_cancel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:10:26.254174+00:00
-- url     : https://prove2.me/theorems/0a9de9a5-4f6b-4417-95f2-e4b7b7f5a790
-- title:
--   DDSmoothness: uh cancel
-- statement:
--   The DDSmoothness construction uses the uh cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMeasurableSet.lean#L27-L35

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.DDSmoothness.uh_cancel {a x : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hax : a * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by sorry
