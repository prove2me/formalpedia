-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_triple_lintegral_product
-- name    : Formalism.FourierDecayAlt.P.S3dx4.triple_lintegral_product
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:00.390582+00:00
-- url     : https://prove2.me/theorems/052d3765-7333-47cf-b753-87f479bdb0d8
-- title:
--   S3dx4: triple lintegral product
-- statement:
--   The S3dx4 construction uses the triple lintegral product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TripleIntegrandMeasurable.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TripleIntegrandMeasurable.lean#L44-L56

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

theorem Formalism.FourierDecayAlt.P.S3dx4.triple_lintegral_product {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x : Formalism.QuantumDeterminants.Mt k r) :
    (∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂μp) *
      (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ ∂μq) =
      ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp := by sorry
