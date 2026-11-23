-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Adm_tail
-- name    : Formalism.FourierDecayAlt.P.Fr11.Adm_tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:10.569806+00:00
-- url     : https://prove2.me/theorems/5b1cde3a-f8de-4e8e-b962-be24bff80ef0
-- title:
--   Fr11: Adm tail
-- statement:
--   The Fr11 construction uses the Adm tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L204-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L204-L210

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (st : Start A)

theorem Formalism.FourierDecayAlt.P.Fr11.Adm_tail (l : Letter ℂ S) (w : List (Letter ℂ S)) (h : admitted st (l :: w)) : admitted st w := by sorry
