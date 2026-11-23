-- Prove2me | Theorems.Thm_Claim_factor_ne_zero
-- name    : Claim.factor_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:43.89381+00:00
-- url     : https://prove2.me/theorems/0dba0559-4195-4b54-8df8-6742edb5f798
-- title:
--   Claim: factor ne zero
-- statement:
--   The Claim construction uses the factor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L7-L21

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

theorem Claim.factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by sorry
