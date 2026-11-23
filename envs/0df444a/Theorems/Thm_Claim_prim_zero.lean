-- Prove2me | Theorems.Thm_Claim_prim_zero
-- name    : Claim.prim_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:51.537405+00:00
-- url     : https://prove2.me/theorems/f8afdf5f-11ae-45d6-81c2-b220c4fe5132
-- title:
--   Claim: prim zero
-- statement:
--   The Claim construction uses the prim zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L23-L33

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

theorem Claim.prim_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by sorry
