-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_sq
-- name    : Formalism.FourierDecayAlt.P.Rec.Pp_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:02.07595+00:00
-- url     : https://prove2.me/theorems/7866fb87-c695-44a3-9c42-6a261f8b9709
-- title:
--   Rec: Pp sq
-- statement:
--   The Rec construction uses the Pp sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L62-L68

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real

theorem Formalism.FourierDecayAlt.P.Rec.Pp_sq {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) :
    Pp e i ^ 2 = ∏ l ∈ Icc 1 i, (1 + e l) := by sorry
