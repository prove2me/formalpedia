-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_mono
-- name    : Formalism.FourierDecayAlt.P.Rec.Pp_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:50.434351+00:00
-- url     : https://prove2.me/theorems/a1b74307-4eb8-4ae3-9d3d-960ce9b399cf
-- title:
--   Rec: Pp mono
-- statement:
--   The Rec construction uses the Pp mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L56-L60

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

theorem Formalism.FourierDecayAlt.P.Rec.Pp_mono {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : Monotone (Pp e) := by sorry
