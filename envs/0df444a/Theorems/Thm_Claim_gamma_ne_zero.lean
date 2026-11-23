-- Prove2me | Theorems.Thm_Claim_gamma_ne_zero
-- name    : Claim.gamma_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:48.425692+00:00
-- url     : https://prove2.me/theorems/4e5fc543-d616-45b2-b213-25bdd49dfbc5
-- title:
--   Claim: gamma ne zero
-- statement:
--   The Claim construction uses the gamma ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L35-L40

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Claim

theorem Claim.gamma_ne_zero {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M) {t : ℂ} (ht : 0 < t.re) :
    DirichletCharacter.gammaFactor φ t ≠ 0 := by sorry
