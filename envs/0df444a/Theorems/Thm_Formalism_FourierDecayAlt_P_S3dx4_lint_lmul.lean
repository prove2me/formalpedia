-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_lint_lmul
-- name    : Formalism.FourierDecayAlt.P.S3dx4.lint_lmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:00.949956+00:00
-- url     : https://prove2.me/theorems/c373ae83-f858-4973-ada2-e35b3db58c1c
-- title:
--   S3dx4: lint lmul
-- statement:
--   The S3dx4 construction uses the lint lmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousSandwichedProduct.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousSandwichedProduct.lean#L28-L31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNSandwich
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
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

theorem Formalism.FourierDecayAlt.P.S3dx4.lint_lmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.lmulM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.lmulM a x) ∂μ = ∫⁻ x, G x ∂μ := by sorry
