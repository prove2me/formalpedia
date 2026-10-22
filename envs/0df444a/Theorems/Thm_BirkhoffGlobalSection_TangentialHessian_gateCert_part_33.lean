-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_33
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_33
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:32:26.311618+00:00
-- url     : https://prove2.me/theorems/fd1c2298-7486-488c-993d-4649db5f8c3d
-- title:
--   Fiber-gate certificate, part 33/35
-- statement:
--   Part 33 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_348` … `gtc_359` of `gt_tree` on their dyadic sub-boxes (31 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 33 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 348–359 (31 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_33 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_348 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_349 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_350 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_351 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_352 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_353 (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_354 (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_355 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_356 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_357 (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_358 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_359 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
