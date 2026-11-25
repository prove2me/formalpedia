-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_exists_compact_tail
-- name    : Formalism.FourierDecayAlt.P.PBK.exists_compact_tail
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:44.998792+00:00
-- url     : https://prove2.me/theorems/916ca964-e44c-4d2a-aad9-4fb8b5879bb1
-- title:
--   PBK: exists compact tail
-- statement:
--   The PBK construction uses the exists compact tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermRealisation.lean#L66-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermRealisation.lean#L66-L108

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.PBK.exists_compact_tail (μ : Measure ℂ) [NullSingletonClass μ] (φ : ℂ → ℝ) (hφ : Integrable φ μ) (η : ℝ) (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D in Kᶜ, φ D ∂μ < η := by sorry
