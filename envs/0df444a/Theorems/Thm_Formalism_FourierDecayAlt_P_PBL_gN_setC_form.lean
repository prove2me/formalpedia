-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_gN_setC_form
-- name    : Formalism.FourierDecayAlt.P.PBL.gN_setC_form
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:29:50.748338+00:00
-- url     : https://prove2.me/theorems/72eb1ce9-a603-508b-bfdd-5e97618edbf0
-- title:
--   PBL: g N set C form
-- statement:
--   The PBL construction uses the g N set C form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L454-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L454-L470

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

theorem Formalism.FourierDecayAlt.P.PBL.gN_setC_form {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (hi : i ≤ S.G.r) (w : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i)
    (hQ : D.IsLocPt Q i) :
    KB.gN (setC S p F) v ε i w P Q =
      ((dW S v i w P Q : ℝ) : ℂ) * (p v).form i hi w
        (KB.slv (p v).T (F v ε) i hi w (stdS S P) ((stdS_size S P).trans hP.2))
        (KB.slv (p v).T (F v ε) i hi w (stdS S Q) ((stdS_size S Q).trans hQ.2)) := by sorry
