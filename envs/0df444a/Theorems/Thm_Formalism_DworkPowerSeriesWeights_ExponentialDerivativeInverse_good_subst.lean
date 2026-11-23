-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_good_subst
-- name    : Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.good_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:05.409884+00:00
-- url     : https://prove2.me/theorems/b17783d2-bcab-4c44-8bba-402dce6dd080
-- title:
--   Exponential Derivative Inverse: good subst
-- statement:
--   The Exponential Derivative Inverse construction uses the good subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L291-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean#L291-L298

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
variable {K : Type u} [NormedField K] {d : ℕ}

theorem Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.good_subst [NeZero d] {K0 : Subfield K} {l : ℕ} {N : ℤ} {be : MvPowerSeries (ZMod d) K}
    (hK0 : InSub K0 be) (hcc : MvPowerSeries.constantCoeff be = 0) (hcb : CongW N (lw l) be)
    {a : ZMod d → MvPowerSeries (V2 d) K} (ha : Fam K0 l a) :
    Good K0 N (fun x : V2 d => lw l x.2) (MvPowerSeries.subst a be) := by sorry
