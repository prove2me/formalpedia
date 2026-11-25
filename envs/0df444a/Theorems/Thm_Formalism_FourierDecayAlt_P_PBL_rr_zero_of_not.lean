-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_rr_zero_of_not
-- name    : Formalism.FourierDecayAlt.P.PBL.rr_zero_of_not
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:02:40.975623+00:00
-- url     : https://prove2.me/theorems/c95bb594-151e-4e64-9a24-75b1db1ff65f
-- title:
--   PBL: rr zero of not
-- statement:
--   The PBL construction uses the rr zero of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L428-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L428-L433

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

theorem Formalism.FourierDecayAlt.P.PBL.rr_zero_of_not {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] {P : M.Par}
    (p : KB.Pl P Wp' Wq') (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp')) (i : ℕ) (w : List C.Letter) (a b : C.LPt)
    (hn : ¬ (D.IsLocPt a i ∧ D.IsLocPt b i)) : p.RR F i w a b = 0 := by sorry
