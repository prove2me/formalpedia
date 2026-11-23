-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_theta_subst
-- name    : Formalism.DworkPowerSeriesWeights.theta_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:00.304127+00:00
-- url     : https://prove2.me/theorems/d4297b7b-3891-433b-baa4-7ecef17897eb
-- title:
--   Dwork Power Series Weights: theta subst
-- statement:
--   The Dwork Power Series Weights construction uses the theta subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L112-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L112-L137

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]

theorem Formalism.DworkPowerSeriesWeights.theta_subst (M Mg A : ZV d N0 N1 → ZV d N0 N1 → K)
    (h : ∀ z i, Mg z i = ∑ y, M z y * A i y) (G : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.subst (linSub Mg) G * mvExp (ε • bSum Mg be) =
      MvPowerSeries.subst
        (fun j : ZV d N0 N1 => (∑ i : ZV d N0 N1, MvPowerSeries.C (A i j) * MvPowerSeries.X i :
          MvPowerSeries (ZV d N0 N1) K))
        (MvPowerSeries.subst (linSub M) G * mvExp (ε • bSum M be)) := by sorry
