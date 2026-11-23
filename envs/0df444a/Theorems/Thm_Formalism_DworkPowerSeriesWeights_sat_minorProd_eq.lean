-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_minorProd_eq
-- name    : Formalism.DworkPowerSeriesWeights.sat_minorProd_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:28.789447+00:00
-- url     : https://prove2.me/theorems/94b0d523-18ed-4929-9982-935b64f7664b
-- title:
--   Dwork Power Series Weights: sat minor Prod eq
-- statement:
--   The Dwork Power Series Weights construction uses the sat minor Prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L178-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L178-L189

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
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
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility

theorem Formalism.DworkPowerSeriesWeights.sat_minorProd_eq (K : Type) [CommRing K] (d N0 C : ℕ) (s : ZMod d) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (A : ∀ c, Fin (p c) → Fin N0) :
    minorProd (fun (i a : Fin N0) => (X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K)) p hp A =
      rename (satEmb d N0 s) (bideterminant K p hp A) := by sorry
