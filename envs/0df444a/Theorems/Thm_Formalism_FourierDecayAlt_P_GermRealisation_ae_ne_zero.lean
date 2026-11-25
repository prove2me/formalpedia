-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_ae_ne_zero
-- name    : Formalism.FourierDecayAlt.P.GermRealisation.ae_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:12.593996+00:00
-- url     : https://prove2.me/theorems/39340817-cf11-4352-a6d9-ae6ae59991aa
-- title:
--   Germ Realisation: ae ne zero
-- statement:
--   The Germ Realisation construction uses the ae ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L99-L100

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

theorem Formalism.FourierDecayAlt.P.GermRealisation.ae_ne_zero : ∀ᵐ z : ℂ, z ≠ 0 := by sorry
