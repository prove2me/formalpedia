-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_ne_of_mem_inv
-- name    : Formalism.FourierDecayAlt.P.Fr11.ne_of_mem_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:33.824213+00:00
-- url     : https://prove2.me/theorems/05529727-fc19-43c1-b4d5-f3e2b6cddf03
-- title:
--   Fr11: ne of mem inv
-- statement:
--   The Fr11 construction uses the ne of mem inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L194-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L194-L202

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

theorem Formalism.FourierDecayAlt.P.Fr11.ne_of_mem_inv (Y : ℂ) :
    ∀ w : List (Letter ℂ S), (∀ l ∈ w, l.plus = true) → Y ∈ (ofWord L st w).inv → ∀ l ∈ w, Y ≠ l.pt
  := by sorry
