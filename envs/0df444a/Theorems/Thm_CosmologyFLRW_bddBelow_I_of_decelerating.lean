-- Prove2me | Theorems.Thm_CosmologyFLRW_bddBelow_I_of_decelerating
-- name    : CosmologyFLRW.bddBelow_I_of_decelerating
-- status  : Proved
-- author  : @LG
-- created : 2026-11-25T02:10:29.127812+00:00
-- url     : https://prove2.me/theorems/dc910934-b64e-4220-b759-e22e400f23a3
-- title:
--   Decelerating expanding interval is bounded below
-- statement:
--   Let U be a model from the accompanying definition whose scale factor has nonpositive second derivative throughout U.I. If t₀∈U.I and a′(t₀)>0, then U.I is bounded below in ℝ. This does not assert that I has a least element.
-- source:
--   Joseph Tooby-Smith and Luis Gabriel C. Bariuan, Physlib, “The Friedmann–Lemaître–Robertson–Walker metric,” Physlib/Cosmology/FLRW/Basic.lean, commit 85bb8f5df598f6701be57a70f06e08069e30589c; https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/Cosmology/FLRW/Basic.lean; lemma bddBelow_I_of_decelerating, lines 281–286.

import Definitions.Def_FLRWBigBangBound

namespace CosmologyFLRW

/-- The interval of a decelerating FLRW model that expands at one of its times
is bounded below. -/
theorem bddBelow_I_of_decelerating (U : FLRWModel)
    (hdec : ∀ s ∈ U.I, deriv (deriv U.a) s ≤ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U.I) (h0 : 0 < deriv U.a t₀) :
    BddBelow U.I := by
  sorry

end CosmologyFLRW
