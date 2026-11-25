-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_level_system_admissible_size
-- name    : Formalism.FourierDecayAlt.P.CutMP.level_system_admissible_size
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:59.724196+00:00
-- url     : https://prove2.me/theorems/078e82ba-1161-5b3e-962d-91ffb214007e
-- title:
--   Cut MP: level system admissible size
-- statement:
--   The Cut MP construction uses the level system admissible size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSystemAdmissibleSize.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSystemAdmissibleSize.lean#L33-L47

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSystemAdmissibleSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField Finset
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.CutMP.level_system_admissible_size (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (hA : D.AdmAt S v a)
    (hI : ∀ x ∈ a, x.2 ∈ Set.Icc (S.cutLo v) (S.cutHi v)) (l : ℕ)
    (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT) (c : LE.Cut) (Lb : ℝ) :
    (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).admitted a ∧
      (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).size a = S.sizeAt v a := by sorry
