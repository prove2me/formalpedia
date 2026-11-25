-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_GermReal_nhat_eq
-- name    : Formalism.FourierDecayAlt.P.GermRealisation.GermReal.nhat_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:01:17.073698+00:00
-- url     : https://prove2.me/theorems/fc371707-9600-4b0b-9b33-8cff3e5e905f
-- title:
--   Germ Real: nhat eq
-- statement:
--   The Germ Real construction uses the nhat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L82-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L82-L97

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

theorem Formalism.FourierDecayAlt.P.GermRealisation.GermReal.nhat_eq {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) {h h' : C.LPt} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ : ℂ) :
    Nhat s R.β R.bt σ h h' = KB.hatB S v ε b s a σ h h' := by sorry
