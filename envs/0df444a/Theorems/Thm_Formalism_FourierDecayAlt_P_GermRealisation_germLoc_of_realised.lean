-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_germLoc_of_realised
-- name    : Formalism.FourierDecayAlt.P.GermRealisation.germLoc_of_realised
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:11.833817+00:00
-- url     : https://prove2.me/theorems/e194aeff-cca7-5310-a5ac-03fa7be3a1ad
-- title:
--   Germ Realisation: germ Loc of realised
-- statement:
--   The Germ Realisation construction uses the germ Loc of realised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L102-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L102-L117

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

theorem Formalism.FourierDecayAlt.P.GermRealisation.germLoc_of_realised {S : C.HidaSetting E Wp Wq} {v : Fin S.f} (hR : GermRealised S v) (hC : GermCont S v) :
    KB.GermLoc S v := by sorry
