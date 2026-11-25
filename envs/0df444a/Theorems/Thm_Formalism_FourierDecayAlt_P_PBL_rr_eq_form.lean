-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_rr_eq_form
-- name    : Formalism.FourierDecayAlt.P.PBL.rr_eq_form
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:56.600337+00:00
-- url     : https://prove2.me/theorems/f6941fbc-ee80-459f-aec0-e5f92165e871
-- title:
--   PBL: rr eq form
-- statement:
--   The PBL construction uses the rr eq form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L15-L20

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem Formalism.FourierDecayAlt.P.PBL.rr_eq_form (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (a b : C.LPt) (ha : D.IsLocPt a j) (hb : D.IsLocPt b j) :
    p.RR F j w a b = p.form j hj w (KB.slv p.T F j hj w a ha.2) (KB.slv p.T F j hj w b hb.2) := by sorry
