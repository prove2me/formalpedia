-- Prove2me | Theorems.Thm_Csg_CSG_safetyOp_gfp_eq_of_certificate
-- name    : Csg.CSG.safetyOp_gfp_eq_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:10:44.971129+00:00
-- url     : https://prove2.me/theorems/e3e66309-d500-4392-91da-4d2e821961d6
-- title:
--   CSG: safety Op gfp eq of certificate
-- statement:
--   **The payoff.** A candidate `v` that is an exact fixed point of `safetyOp`, and that
--       upper-bounds every post-fixed point of `safetyOp`, *is* the greatest fixed point -- the dual of
--       `reachOp_lfp_eq_of_certificate`, specialising the fully generic `OrderHom.gfp_eq_of_certificate`
--       above to `f := C.safetyOp safe hr`. Callers still have to supply `hfixed`/`hub` themselves:
--       this combinator automates the assembly of the two pinning lemmas via `le_antisymm`, not the two
--       mathematical facts underneath it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SafetyCertificate.lean#L51-L56
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SafetyCertificate.lean#L51-L56

import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_SafetyCertificate
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.safetyOp_gfp_eq_of_certificate (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1)
    (hfixed : C.safetyOp safe hr v = v)
    (hub : ∀ b, b ≤ C.safetyOp safe hr b → b ≤ v) :
    (C.safetyOp safe hr).gfp = v := by sorry
