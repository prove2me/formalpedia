-- Prove2me | Theorems.Thm_Csg_CSG_reachOp_lfp_eq_of_certificate
-- name    : Csg.CSG.reachOp_lfp_eq_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:51:54.26453+00:00
-- url     : https://prove2.me/theorems/a0c713bd-b859-4781-a35c-52cce62c68b8
-- title:
--   CSG: reach Op lfp eq of certificate
-- statement:
--   **The payoff.** A candidate `v` that is an exact fixed point of `reachOp`, and that
--       lower-bounds every pre-fixed point of `reachOp`, *is* the least fixed point -- the
--       Knaster-Tarski pinning argument, generalised from `RockPaperScissorsLfp.lean`'s
--       `rpsVStar`-specific proof to an arbitrary `CSG`, goal, and candidate. Callers still have to
--       supply `hfixed`/`hlb` themselves: this combinator automates the assembly of the two pinning
--       lemmas via `le_antisymm`, not the two mathematical facts underneath it. A one-line wrapper
--       around the fully generic `OrderHom.lfp_eq_of_certificate` above, specialising its `f` to
--       `C.reachOp goal hr`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachCertificate.lean#L58-L63
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachCertificate.lean#L58-L63

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_ReachCertificate
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.reachOp_lfp_eq_of_certificate (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1)
    (hfixed : C.reachOp goal hr v = v)
    (hlb : ∀ b, C.reachOp goal hr b ≤ b → v ≤ b) :
    (C.reachOp goal hr).lfp = v := by sorry
