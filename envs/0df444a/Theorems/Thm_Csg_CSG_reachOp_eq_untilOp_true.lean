-- Prove2me | Theorems.Thm_Csg_CSG_reachOp_eq_untilOp_true
-- name    : Csg.CSG.reachOp_eq_untilOp_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:47:58.918882+00:00
-- url     : https://prove2.me/theorems/cdfd208d-974e-46ec-be9f-d24a5dbe0955
-- title:
--   CSG: reach Op eq until Op true
-- statement:
--   **The payoff, fully general.** Plain reachability is `until`'s special case with a trivially
--       always-safe predicate -- `reachOp` and `untilOp (fun _ => True)` are *the same operator*, not
--       merely operators that happen to agree on one instance (`RockPaperScissorsUntil.lean`'s own
--       `rpsCSG_untilOp_lfp_eq_reachOp_lfp` was exactly that weaker, instance-specific fact; this is the
--       statement it was concrete evidence for). `change` jumps past the `OrderHom`/`FunLike` coercion
--       to bare `reachOpFun`/`untilOpFun` application (pure defeq, independent of either condition's
--       truth value); `by_cases hg : goal s` plus
--       `simp only [reachOpFun, untilOpFun, if_pos/if_neg hg]` then handles the abstract
--       `goal`
--       condition, the same idiom `untilOpFun_mono` already uses safely.
--       The concrete condition `(fun _ => True) s` is never named in a supplied lemma -- left for
--       `simp`'s own ground-decidable normalisation to collapse unopposed, which is exactly what closes
--       the `if_neg hg` branch once `goal`'s split is out of the way.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/UntilOp.lean#L136-L147
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/UntilOp.lean#L136-L147

import Definitions.Def_Csg_CsgMonotone
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_UntilOp
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.reachOp_eq_untilOp_true (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    C.reachOp goal hr = C.untilOp (fun _ => True) goal hr := by sorry
