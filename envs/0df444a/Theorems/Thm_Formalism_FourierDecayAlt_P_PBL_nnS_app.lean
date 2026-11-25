-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_nnS_app
-- name    : Formalism.FourierDecayAlt.P.PBL.nnS_app
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:58:47.459439+00:00
-- url     : https://prove2.me/theorems/ac04d3b2-8d55-43f3-bd08-349969f2a942
-- title:
--   PBL: nn S app
-- statement:
--   The PBL construction uses the nn S app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L205-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L205-L211

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.PBL.nnS_app (S : C.HidaSetting E Wp Wq) (j : ℕ) (hj : j ≤ S.G.r) (H : C.LPt) (c : ℂ) (hH : D.ptSize H = j) :
    nnS S (H ++ [(1, c)]) = nnS S H *
      C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] := by sorry
