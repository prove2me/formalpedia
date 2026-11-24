-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_expand
-- name    : Formalism.FourierDecayAlt.P.PBA.expand
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:36.010313+00:00
-- url     : https://prove2.me/theorems/54c9892b-09f2-4280-94e2-36c26fea2d3b
-- title:
--   PBA: expand
-- statement:
--   The PBA construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L188-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L188-L221

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
variable {S}
variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}

theorem Formalism.FourierDecayAlt.P.PBA.expand (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v))
    (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop)
    (F : Fin S.f → List C.Letter → ℂ) :
    ∑ w' ∈ S.base.Wb n, (pθ S A w θ w' : ℂ) * ∏ v, F v (w'.1 v) =
      ∏ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) * F v a else F v (w.1 v)) := by sorry
