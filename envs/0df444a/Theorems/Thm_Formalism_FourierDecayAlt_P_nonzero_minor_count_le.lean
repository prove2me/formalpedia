-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_nonzero_minor_count_le
-- name    : Formalism.FourierDecayAlt.P.nonzero_minor_count_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:41:09.17569+00:00
-- url     : https://prove2.me/theorems/e3865546-dcea-4467-bf82-49f133de7d4c
-- title:
--   P: nonzero minor count le
-- statement:
--   The P construction uses the nonzero minor count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensityLemmaOfReductions.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensityLemmaOfReductions.lean#L11-L16

import Definitions.Def_Formalism_HermitianCurvature_LemmaDensOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensityLemmaOfReductions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem Formalism.FourierDecayAlt.P.nonzero_minor_count_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ ≤ r + 2 := by sorry
