-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_mem_Lp
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.mem_Lp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:50.570327+00:00
-- url     : https://prove2.me/theorems/d1993822-076b-4896-ba24-0589bd42f913
-- title:
--   Real Weighted Forms: mem Lp
-- statement:
--   The Real Weighted Forms construction uses the mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L167-L171

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

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.mem_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (a : Fin K) :
    (⟨true, sl a, (y a : ℂ)⟩ : Letter ℂ S) ∈ Lp sl y := by sorry
