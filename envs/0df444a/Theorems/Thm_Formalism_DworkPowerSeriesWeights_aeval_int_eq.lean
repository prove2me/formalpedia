-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_aeval_int_eq
-- name    : Formalism.DworkPowerSeriesWeights.aeval_int_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:32.561114+00:00
-- url     : https://prove2.me/theorems/b4ccd282-ff4a-4962-afcb-180388788fd9
-- title:
--   Dwork Power Series Weights: aeval int eq
-- statement:
--   The Dwork Power Series Weights construction uses the aeval int eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L223-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L223-L228

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.aeval_int_eq {σ A K : Type} [CommRing A] [CommRing K] [Algebra ℤ K]
    (ι : MvPolynomial σ A →+* K) (P : MvPolynomial σ ℤ) :
    aeval (fun i => ι (X i)) P = ι (MvPolynomial.map (Int.castRingHom A) P) := by sorry
