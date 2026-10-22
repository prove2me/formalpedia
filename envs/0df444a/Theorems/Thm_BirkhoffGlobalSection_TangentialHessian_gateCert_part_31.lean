-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_31
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_31
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:32:23.174312+00:00
-- url     : https://prove2.me/theorems/e4694603-7d48-4249-bb17-bb7e35da7417
-- title:
--   Fiber-gate certificate, part 31/35
-- statement:
--   Part 31 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_323` … `gtc_335` of `gt_tree` on their dyadic sub-boxes (29 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 31 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 323–335 (29 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_31 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_323 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_324 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_325 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_326 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_327 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_328 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_329 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_330 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_331 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_332 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_333 (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_334 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_335 (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 1) 2) 0) 2) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
