-- Prove2me | Theorems.Thm_Csg_CSG_safetyOp_gfp_mem_Icc_of_certificate
-- name    : Csg.CSG.safetyOp_gfp_mem_Icc_of_certificate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:26:53.888674+00:00
-- url     : https://prove2.me/theorems/7326cec3-ef19-4e68-abeb-d589ab51e72c
-- title:
--   CSG: safety Op gfp mem Icc of certificate
-- statement:
--   The safety specialisation of `OrderHom.gfp_mem_Icc_of_certificate`, dual to
--       `reachOp_lfp_mem_Icc_of_certificate` above exactly as `CSG.safetyOp_gfp_eq_of_certificate` is
--       dual to `CSG.reachOp_lfp_eq_of_certificate`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L92-L96
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L92-L96

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.safetyOp_gfp_mem_Icc_of_certificate (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (lo hi : S → Set.Icc (0 : ℝ) 1)
    (hpost : lo ≤ C.safetyOp safe hr lo) (hub : ∀ b, b ≤ C.safetyOp safe hr b → b ≤ hi) :
    lo ≤ (C.safetyOp safe hr).gfp ∧ (C.safetyOp safe hr).gfp ≤ hi := by sorry
