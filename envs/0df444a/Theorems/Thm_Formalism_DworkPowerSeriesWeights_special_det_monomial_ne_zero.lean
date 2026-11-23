-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_special_det_monomial_ne_zero
-- name    : Formalism.DworkPowerSeriesWeights.special_det_monomial_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:36.982918+00:00
-- url     : https://prove2.me/theorems/66248da2-b0b1-4909-9fb1-c0242fe11fb4
-- title:
--   Dwork Power Series Weights: special det monomial ne zero
-- statement:
--   The Dwork Power Series Weights construction uses the special det monomial ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L35-L50

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
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

theorem Formalism.DworkPowerSeriesWeights.special_det_monomial_ne_zero {n σ R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [Nontrivial R] (E : n → n → σ →₀ ℕ)
    (hE : Function.Injective fun p : Equiv.Perm n => ∑ c, E (p c) c) :
    (Matrix.of fun r c => (MvPolynomial.monomial (E r c) (1 : R))).det ≠ 0 := by sorry
