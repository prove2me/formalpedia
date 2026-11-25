-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_abar_ae_eq
-- name    : Formalism.FourierDecayAlt.P.PBK.abar_ae_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:33:29.778823+00:00
-- url     : https://prove2.me/theorems/743a3a03-a5eb-5132-babe-a1d61c7114d0
-- title:
--   PBK: abar ae eq
-- statement:
--   The PBK construction uses the abar ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L38-L44

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.abar_ae_eq {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) :
    abar s ε bt =ᵐ[volume] fun D => ∑ k ∈ Finset.range s, ‖bt (NthRootMeasurability.R s k (ε * D))‖ := by sorry
