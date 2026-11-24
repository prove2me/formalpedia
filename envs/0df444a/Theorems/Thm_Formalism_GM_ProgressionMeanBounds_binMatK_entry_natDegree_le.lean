-- Prove2me | Theorems.Thm_Formalism_GM_ProgressionMeanBounds_binMatK_entry_natDegree_le
-- name    : Formalism.GM.ProgressionMeanBounds.binMatK_entry_natDegree_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:00.181806+00:00
-- url     : https://prove2.me/theorems/f918bfb3-2ad0-4857-9e43-1104a050a2b6
-- title:
--   Progression Mean Bounds: bin Mat K entry nat Degree le
-- statement:
--   The Progression Mean Bounds construction uses the bin Mat K entry nat Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L48-L54

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

theorem Formalism.GM.ProgressionMeanBounds.binMatK_entry_natDegree_le (K : Type) [Field K] {n : ℕ} (del₀ : ℕ)
    (c : Fin n → Fin n → ℕ → K) (i j : Fin n) : ((binMatK K del₀ c) i j).natDegree ≤ del₀ := by sorry
