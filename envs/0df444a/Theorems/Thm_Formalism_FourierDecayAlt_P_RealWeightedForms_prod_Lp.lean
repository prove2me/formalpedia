-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_prod_Lp
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.prod_Lp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:19:04.760146+00:00
-- url     : https://prove2.me/theorems/c44ee9ab-4a38-43f4-bf1a-b85d2f55cce2
-- title:
--   Real Weighted Forms: prod Lp
-- statement:
--   The Real Weighted Forms construction uses the prod Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L181-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L181-L185

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

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.prod_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (g : ℂ → ℂ) :
    ((Lp sl y).map fun l => g l.pt).prod = ∏ a, g (y a) := by sorry
