-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_pow_ne
-- name    : Formalism.InvariantFactorPaths.L4.eW_pow_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:26.909191+00:00
-- url     : https://prove2.me/theorems/d2ea30ce-d70e-4bba-9f88-970828a7f270
-- title:
--   L4: e W pow ne
-- statement:
--   The L4 construction uses the e W pow ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L243-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L243-L256

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.eW_pow_ne (a a' : Fin r) (haa : a ≠ a') : ∀ (i : ℕ) (γ : Fin r → ℤ)
    (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), z ∈ WS p K γ → z ≠ 0 → (i : ℤ) ≤ γ a' → 0 ≤ γ a →
    ((eW p K a a') ^ i) z ≠ 0 := by sorry
