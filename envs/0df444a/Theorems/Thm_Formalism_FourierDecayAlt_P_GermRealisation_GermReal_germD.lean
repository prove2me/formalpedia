-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_GermReal_germD
-- name    : Formalism.FourierDecayAlt.P.GermRealisation.GermReal.germD
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:04.978664+00:00
-- url     : https://prove2.me/theorems/36db9676-9c1f-5e31-8677-22229ec83d6a
-- title:
--   Germ Real: germ D
-- statement:
--   The Germ Real construction uses the germ D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L66-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean#L66-L80

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

theorem Formalism.FourierDecayAlt.P.GermRealisation.GermReal.germD {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) (hs : 2 ≤ s) (B : ℝ)
    (hB : ∀ h ∈ Y, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + s - 2) a (h ++ [(s - 1, t)]) (h ++ [(s - 1, t)])‖ ≤ B) :
    GermD s R.β R.ε' Y R.ut R.bt B := by sorry
