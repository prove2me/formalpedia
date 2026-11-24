-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_admissible_word_pairwise_condition
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_word_pairwise_condition
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:19:39.670801+00:00
-- url     : https://prove2.me/theorems/3dd7380e-9dec-47e0-ad83-7e0a6d9659a1
-- title:
--   Real Weighted Forms: admissible word pairwise condition
-- statement:
--   The Real Weighted Forms construction uses the admissible word pairwise condition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L31-L35

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
variable {S : Type}

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_word_pairwise_condition {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) :
    w.Pairwise (fun l l' => Cnd l l' ∧ Cnd l' l) := by sorry
