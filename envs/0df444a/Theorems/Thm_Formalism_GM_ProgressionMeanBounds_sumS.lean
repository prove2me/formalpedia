-- Prove2me | Theorems.Thm_Formalism_GM_ProgressionMeanBounds_sumS
-- name    : Formalism.GM.ProgressionMeanBounds.sumS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:10.162982+00:00
-- url     : https://prove2.me/theorems/cc30aaf8-e52d-4faa-8228-16ea6e3cb90d
-- title:
--   Progression Mean Bounds: sum S
-- statement:
--   The Progression Mean Bounds construction uses the sum S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L21-L36

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

theorem Formalism.GM.ProgressionMeanBounds.sumS (p : ℝ) (hp : 2 ≤ p) (Y₀ h : ℕ) :
    ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) ≤ (Y₀ : ℝ) / (p - 1) + h := by sorry
