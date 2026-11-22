-- Prove2me | Theorems.Thm_Csg_CSG_reachOp_lfp_mem_Icc_of_certificate
-- name    : Csg.CSG.reachOp_lfp_mem_Icc_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:53:36.504751+00:00
-- url     : https://prove2.me/theorems/2f72fd85-77dc-4b60-bcd1-2d9ade7614e6
-- title:
--   CSG: reach Op lfp mem Icc of certificate
-- statement:
--   The reachability specialisation of `OrderHom.lfp_mem_Icc_of_certificate`, exactly the way
--       `CSG.reachOp_lfp_eq_of_certificate` specialises the exact-pinning version.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L83-L87
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L83-L87

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.reachOp_lfp_mem_Icc_of_certificate (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (lo hi : S → Set.Icc (0 : ℝ) 1)
    (hlb : ∀ b, C.reachOp goal hr b ≤ b → lo ≤ b) (hpre : C.reachOp goal hr hi ≤ hi) :
    lo ≤ (C.reachOp goal hr).lfp ∧ (C.reachOp goal hr).lfp ≤ hi := by sorry
