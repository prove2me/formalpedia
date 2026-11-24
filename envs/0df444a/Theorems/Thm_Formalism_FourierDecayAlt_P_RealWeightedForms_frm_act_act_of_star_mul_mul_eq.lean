-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_frm_act_act_of_star_mul_mul_eq
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.frm_act_act_of_star_mul_mul_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:19:05.168978+00:00
-- url     : https://prove2.me/theorems/6d13cd9d-1de0-4d07-bba3-055165f8aa53
-- title:
--   Real Weighted Forms: frm act act of star mul mul eq
-- statement:
--   The Real Weighted Forms construction uses the frm act act of star mul mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L157-L163

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
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.frm_act_act_of_star_mul_mul_eq (ρ : Rep A V) (RR W : SlopeTestRemainingChoices S A) (hW : star W * RR * W = RR) (X X' : Ix S → V) :
    frm ρ RR (act W X) (act W X') = frm ρ RR X X' := by sorry
