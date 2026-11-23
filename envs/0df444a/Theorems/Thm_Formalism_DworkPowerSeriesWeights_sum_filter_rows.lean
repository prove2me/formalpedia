-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_filter_rows
-- name    : Formalism.DworkPowerSeriesWeights.sum_filter_rows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:43.048543+00:00
-- url     : https://prove2.me/theorems/c62b6263-40bf-45ba-8f20-4f95a915b0f0
-- title:
--   Dwork Power Series Weights: sum filter rows
-- statement:
--   The Dwork Power Series Weights construction uses the sum filter rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L299-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L299-L310

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
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
open Formalism.IncomingBounds MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.sum_filter_rows {d N0 N1 : ℕ} [NeZero d] (Pr : ZMod d × Fin N0 → Prop) [DecidablePred Pr]
    (κ : ZV d N0 N1 →₀ ℕ) :
    (∑ y ∈ Finset.univ.filter (fun y : ZV d N0 N1 => Pr (y.1, y.2.1)), κ y) =
      ∑ r ∈ Finset.univ.filter Pr, rowDeg r.1 r.2 κ := by sorry
