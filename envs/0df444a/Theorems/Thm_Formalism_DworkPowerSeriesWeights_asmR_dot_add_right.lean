-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_add_right
-- name    : Formalism.DworkPowerSeriesWeights.asmR_dot_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:49.363775+00:00
-- url     : https://prove2.me/theorems/dbf24f55-0168-4eda-951d-0c6ce26d661f
-- title:
--   Dwork Power Series Weights: asm R dot add right
-- statement:
--   The Dwork Power Series Weights construction uses the asm R dot add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L25-L29

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.asmR_dot_add_right {ι : Type v} (n : ι →₀ ℕ) (r s : ι → ℝ) :
    dot n (fun i => r i + s i) = dot n r + dot n s := by sorry
