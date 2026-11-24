-- Prove2me | Theorems.Thm_Formalism_GM_ProgressionMeanBounds_geom
-- name    : Formalism.GM.ProgressionMeanBounds.geom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:03.966739+00:00
-- url     : https://prove2.me/theorems/fa12d38c-313d-4cf1-ae98-1fbf51230c51
-- title:
--   Progression Mean Bounds: geom
-- statement:
--   The Progression Mean Bounds construction uses the geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L10-L19

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Formalism.GM.ProgressionMeanBounds
open Finset Polynomial

theorem Formalism.GM.ProgressionMeanBounds.geom (p : ℝ) (hp : 2 ≤ p) (h : ℕ) :
    ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i = (1 - 1 / p ^ h) / (p - 1) := by sorry
