-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_geom_le
-- name    : Formalism.FourierDecayAlt.P.Rec.geom_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:04.592583+00:00
-- url     : https://prove2.me/theorems/3bb86b02-240c-4904-bfb3-7a27f1d5d3df
-- title:
--   Rec: geom le
-- statement:
--   The Rec construction uses the geom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L8-L29

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

theorem Formalism.FourierDecayAlt.P.Rec.geom_le (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1/2) :
    ∀ i : ℕ, ∑ t ∈ Icc 2 i, a ^ (t-1) ≤ 2 * a := by sorry
