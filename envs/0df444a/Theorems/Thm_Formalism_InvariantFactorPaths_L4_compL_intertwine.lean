-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_intertwine
-- name    : Formalism.InvariantFactorPaths.L4.compL_intertwine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:59:07.818823+00:00
-- url     : https://prove2.me/theorems/3943c248-a738-4344-a104-00d71c8d5116
-- title:
--   L4: comp L intertwine
-- statement:
--   The L4 construction uses the comp L intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L71-L77

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {k σ : Type} [Field k]

theorem Formalism.InvariantFactorPaths.L4.compL_intertwine (T : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (Pr Pr' : (σ →₀ ℕ) → Prop)
    (h1 : ∀ x ∈ restrictSupport k {m | Pr' m}, T x ∈ restrictSupport k {m | Pr m})
    (h2 : ∀ x ∈ restrictSupport k {m | ¬ Pr' m}, T x ∈ restrictSupport k {m | ¬ Pr m}) (x : MvPolynomial σ k) :
    compL k Pr (T x) = T (compL k Pr' x) := by sorry
