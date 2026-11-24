-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_qw_pos
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.qw_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:19:22.50836+00:00
-- url     : https://prove2.me/theorems/a5034fde-a9c3-4a0c-a765-153f7f466f23
-- title:
--   Real Weighted Forms: qw pos
-- statement:
--   The Real Weighted Forms construction uses the qw pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L80-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L80-L108

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

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.qw_pos (q : ℂ → ℂ) (Y : ℝ) (hq : (q Y).im = 0 ∧ 0 < (q Y).re) :
    ∀ w : List (Letter ℂ S), (∀ l' ∈ w, l'.pt.im = 0 ∧ CndY Y l') →
      (qw q w (Y : ℂ)).im = 0 ∧ 0 < (qw q w (Y : ℂ)).re := by sorry
