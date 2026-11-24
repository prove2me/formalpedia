-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_triple_integrand_measurable
-- name    : Formalism.FourierDecayAlt.P.S3dx4.triple_integrand_measurable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:26:57.180799+00:00
-- url     : https://prove2.me/theorems/17982785-5260-459d-9d8a-322f8cd4a58d
-- title:
--   S3dx4: triple integrand measurable
-- statement:
--   The S3dx4 construction uses the triple integrand measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TripleIntegrandMeasurable.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TripleIntegrandMeasurable.lean#L33-L42

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.triple_integrand_measurable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    {X : α → Formalism.QuantumDeterminants.Mt k r} {Pp Qq : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Continuous X) (hP : Continuous Pp) (hQ : Continuous Qq) :
    Measurable (fun t => Phi3 e1 e2 γi (X t) (Pp t) (Qq t)) := by sorry
