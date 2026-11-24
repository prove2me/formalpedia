-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_pow_div
-- name    : Formalism.InvariantFactorPaths.L4.exists_pow_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:57.95106+00:00
-- url     : https://prove2.me/theorems/f9f6c83a-d973-4471-8af7-0079574f9e72
-- title:
--   L4: exists pow div
-- statement:
--   The L4 construction uses the exists pow div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L61-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L61-L77

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.L4.exists_pow_div (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p])
    (hf : f ∈ restrictSupport ℚ_[p] {m : σ →₀ ℕ | e ≤ m v}) : ∃ h, f = X v ^ e * h := by sorry
