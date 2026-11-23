-- Prove2me | Theorems.Thm_Csg_CSG_rewardUntilOp_eq_of_gfp_certificate
-- name    : Csg.CSG.rewardUntilOp_eq_of_gfp_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:44.329806+00:00
-- url     : https://prove2.me/theorems/6daf04bc-6dec-4842-8378-eb23aebf3797
-- title:
--   CSG: reward Until Op eq of gfp certificate
-- statement:
--   **The payoff, min/zero-reward-cycle version.** A candidate `v` that is a fixed point of
--       `rewardUntilStep`, together with a proof that it *dominates* every other fixed point (rather
--       than being the *only* one -- see the module docstring's worked example for why `∃!` fails
--       here), witnesses that `v` is *the* fixed point dominating every fixed point, and that this
--       dominating fixed point is unique. The order-theoretic analogue of `safetyOp`'s `.gfp`, stated
--       by hand since plain `S → ℝ` has no `CompleteLattice` to hang an automatic `.gfp` on. As with
--       `rewardUntilOp_eq_of_certificate`, this combinator automates only the assembly: `hfixed` and
--       `hub` are still model-specific mathematics the caller must supply.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RewardUntilCertificate.lean#L122-L127
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RewardUntilCertificate.lean#L122-L127

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_RewardUntilCertificate
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.rewardUntilOp_eq_of_gfp_certificate (goal : S → Prop) [DecidablePred goal] (v : S → ℝ)
    (hfixed : C.rewardUntilStep goal v = v)
    (hub : ∀ w : S → ℝ, C.rewardUntilStep goal w = w → w ≤ v) :
    ∃! w : S → ℝ, C.rewardUntilStep goal w = w ∧
      ∀ u : S → ℝ, C.rewardUntilStep goal u = u → u ≤ w := by sorry
