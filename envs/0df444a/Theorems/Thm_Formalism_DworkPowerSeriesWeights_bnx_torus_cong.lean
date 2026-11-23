-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_torus_cong
-- name    : Formalism.DworkPowerSeriesWeights.bnx_torus_cong
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:40.03501+00:00
-- url     : https://prove2.me/theorems/4b104baa-054a-424d-91b2-8a0b3896134b
-- title:
--   Dwork Power Series Weights: bnx torus cong
-- statement:
--   The Dwork Power Series Weights construction uses the bnx torus cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L600-L649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L600-L649

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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
open MvPowerSeries Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.bnx_torus_cong {K : Type u} [Field K] (l d : ℕ) [NeZero d] (hl : l.Prime) (hl3 : 3 ≤ l)
    (hd2 : 2 ≤ d) (hde : Even d) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) K) (htor : subst (torus l ζ) be = be)
    (s s' : ZMod d) (hs : s.val % 2 = 0) (hs' : s'.val % 2 ≠ 0) (α β : ℕ)
    (hc : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0) :
    s + (α : ZMod d) = s' + (β : ZMod d) := by sorry
