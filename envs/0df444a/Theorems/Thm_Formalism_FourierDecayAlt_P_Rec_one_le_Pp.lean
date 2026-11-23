-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_one_le_Pp
-- name    : Formalism.FourierDecayAlt.P.Rec.one_le_Pp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:04.396131+00:00
-- url     : https://prove2.me/theorems/15048f00-a7d1-4b82-a150-ce4297a60242
-- title:
--   Rec: one le Pp
-- statement:
--   The Rec construction uses the one le Pp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L44-L51

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

theorem Formalism.FourierDecayAlt.P.Rec.one_le_Pp {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : ∀ i, 1 ≤ Pp e i := by sorry
