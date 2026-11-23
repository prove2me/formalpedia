-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ringMap_minorProd
-- name    : Formalism.DworkPowerSeriesWeights.ringMap_minorProd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:30.597127+00:00
-- url     : https://prove2.me/theorems/079a8362-ae66-408c-a98d-9c903c344237
-- title:
--   Dwork Power Series Weights: ring Map minor Prod
-- statement:
--   The Dwork Power Series Weights construction uses the ring Map minor Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L28-L37

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

theorem Formalism.DworkPowerSeriesWeights.ringMap_minorProd {R S : Type} [CommRing R] [CommRing S] {σ : Type} {N0 N1 C : ℕ}
    (ψ : MvPolynomial σ R →+* MvPolynomial σ S)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    ψ (minorProd row p hp I) = minorProd (fun i b => ψ (row i b)) p hp I := by sorry
