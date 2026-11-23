-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mem_inv_of
-- name    : Formalism.FourierDecayAlt.P.Fr11.mem_inv_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:56.17037+00:00
-- url     : https://prove2.me/theorems/07251a8e-b7ef-4c84-bd59-d5bd7e92b52b
-- title:
--   Fr11: mem inv of
-- statement:
--   The Fr11 construction uses the mem inv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L185-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L185-L192

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

theorem Formalism.FourierDecayAlt.P.Fr11.mem_inv_of (P : ℂ) (hP : P ∈ st.inv) :
    ∀ w : List (Letter ℂ S), (∀ l ∈ w, l.plus = true) → (∀ l ∈ w, P - l.pt ≠ 0 ∧ P - l.pt ≠ 1) →
      P ∈ (ofWord L st w).inv
  := by sorry
