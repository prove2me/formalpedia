-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_integral_inner_self_eq
-- name    : Formalism.FourierDecayAlt.P.GermRealisation.integral_inner_self_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:50.220802+00:00
-- url     : https://prove2.me/theorems/b26c250b-c7a9-54b5-8cf8-816b6e78283b
-- title:
--   Germ Realisation: integral inner self eq
-- statement:
--   The Germ Realisation construction uses the integral inner self eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L57-L64

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocTail
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfRealised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
attribute [instance] GermReal.nag GermReal.ips GermReal.cs

theorem Formalism.FourierDecayAlt.P.GermRealisation.integral_inner_self_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : ℂ → H) :
    ∫ c, ⟪f c, f c⟫_ℂ = ((∫ c, ‖f c‖ ^ 2 : ℝ) : ℂ) := by sorry
