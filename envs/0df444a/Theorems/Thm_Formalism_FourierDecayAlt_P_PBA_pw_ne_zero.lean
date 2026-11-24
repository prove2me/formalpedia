-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_pw_ne_zero
-- name    : Formalism.FourierDecayAlt.P.PBA.pw_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:17.913652+00:00
-- url     : https://prove2.me/theorems/74901e84-ef1e-4f70-b424-44ec3266659d
-- title:
--   PBA: pw ne zero
-- statement:
--   The PBA construction uses the pw ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L155-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L155-L163

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

theorem Formalism.FourierDecayAlt.P.PBA.pw_ne_zero (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v)) {v : Fin S.f} {a : List C.Letter}
    (h : pw S A w θ v a ≠ 0) : a ∈ supp S A w U v := by sorry
