-- Prove2me | Theorems.Thm_Csg_CSG_rewardUntilOp_eq_of_certificate
-- name    : Csg.CSG.rewardUntilOp_eq_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:20:56.499896+00:00
-- url     : https://prove2.me/theorems/bc749e9a-6045-4850-94a4-4d049a3b484a
-- title:
--   CSG: reward Until Op eq of certificate
-- statement:
--   **The payoff.** A candidate `v` that is an exact fixed point of `rewardUntilStep`, together
--       with a proof that *any* real-valued fixed point of the same step equals `v`, witnesses that
--       `rewardUntilStep goal` has a unique fixed point, namely `v` -- the reward-until-absorption
--       analogue of `reachOp_lfp_eq_of_certificate`/`OrderHom.lfp_eq_of_certificate`, stated as an
--       `∃!` rather than an `.lfp` equation since plain `S → ℝ` carries no complete-lattice structure
--       to hang a canonical least fixed point on here. Generalises `RockPaperScissorsSteps.lean`'s
--       `rpsSteps_fixed`/`rpsSteps_unique` pair (which are exactly `hfixed`/`huniq` for
--       `rpsCSGSteps`/`rpsStepsStep`/`rpsSteps`) into a single reusable statement for an arbitrary
--       `CSG`, `goal`, and candidate. As with `ReachCertificate.lean`, this combinator automates only
--       the assembly of the two hypotheses into the `∃!` conclusion, not the (model-specific)
--       mathematics of `hfixed`/`huniq` themselves.
--
--       **Caveat:** sound only for models with no reachable zero-reward cycle outside `goal` --
--       `huniq` is not just hard to prove but outright false otherwise (see the module docstring
--       above, and `rewardUntilOp_eq_of_gfp_certificate` below for that case).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RewardUntilCertificate.lean#L108-L112
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RewardUntilCertificate.lean#L108-L112

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_RewardUntilCertificate
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.rewardUntilOp_eq_of_certificate (goal : S → Prop) [DecidablePred goal] (v : S → ℝ)
    (hfixed : C.rewardUntilStep goal v = v)
    (huniq : ∀ w : S → ℝ, C.rewardUntilStep goal w = w → w = v) :
    ∃! w : S → ℝ, C.rewardUntilStep goal w = w := by sorry
