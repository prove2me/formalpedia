-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_germLoc_of_fibres
-- name    : Formalism.FourierDecayAlt.P.GermRealisation.germLoc_of_fibres
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:41.182639+00:00
-- url     : https://prove2.me/theorems/927ec100-43aa-43df-b4c0-aa0c545c6d80
-- title:
--   Germ Realisation: germ Loc of fibres
-- statement:
--   The Germ Realisation construction uses the germ Loc of fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfFibres.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfFibres.lean#L155-L160

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfRealised
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfFibres
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
attribute [instance] FibreGerm.nag FibreGerm.ips FibreGerm.cs

theorem Formalism.FourierDecayAlt.P.GermRealisation.germLoc_of_fibres {S : C.HidaSetting E Wp Wq} {v : Fin S.f} (hI : JC.ThmPIntPlace S v fun i => KB.dlB S i 1)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hF : GermFibres S v) (hC : GermCont S v) : KB.GermLoc S v := by sorry
