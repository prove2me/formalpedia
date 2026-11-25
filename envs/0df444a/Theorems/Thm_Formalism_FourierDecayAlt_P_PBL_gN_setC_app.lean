-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_gN_setC_app
-- name    : Formalism.FourierDecayAlt.P.PBL.gN_setC_app
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:42:59.857+00:00
-- url     : https://prove2.me/theorems/2059e32f-b5e3-5e0a-9a01-cd9026bbecdc
-- title:
--   PBL: g N set C app
-- statement:
--   The PBL construction uses the g N set C app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L213-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean#L213-L306

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

theorem Formalism.FourierDecayAlt.P.PBL.gN_setC_app {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) (c : ℂ) (hc : c ≠ 0) :
    KB.gN (setC S p F) v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) =
      ((Kc S v j w h h' : ℝ) : ℂ) * ((KB.levW (D.parOf S v) (j + 1) ((lamS S j : ℂ) * c) : ℝ) : ℂ) *
        (p v).RR (F v ε) (j + 1) w (stdS S h ++ [(1, (lamS S j : ℂ) * c)])
          (stdS S h' ++ [(1, (lamS S j : ℂ) * c)]) := by sorry
