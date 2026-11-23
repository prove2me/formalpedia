-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_frameA_frob_norm
-- name    : Formalism.DworkPowerSeriesWeights.frameA_frob_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:29.793814+00:00
-- url     : https://prove2.me/theorems/7d89a759-3884-40fa-898e-61598313fa2c
-- title:
--   Dwork Power Series Weights: frame A frob norm
-- statement:
--   The Dwork Power Series Weights construction uses the frame A frob norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FrameA.lean#L15-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FrameA.lean#L15-L46

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementK
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.frameA_frob_norm {K : Type*} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hl : l.Prime) {ι : Type*} (U : ι → K) (hU : ∀ a, ‖U a‖ ≤ 1) (e : ℕ) (S : Finset ι) :
    ‖(∑ a ∈ S, U a) ^ (l ^ e) - ∑ a ∈ S, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by sorry
