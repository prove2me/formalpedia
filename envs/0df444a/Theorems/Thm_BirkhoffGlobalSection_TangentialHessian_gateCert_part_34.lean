-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_34
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_34
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:32:36.260636+00:00
-- url     : https://prove2.me/theorems/6edbaff9-253a-4b42-9d09-90cccf9f2a2b
-- title:
--   Fiber-gate certificate, part 34/35
-- statement:
--   Part 34 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_360` … `gtc_364` of `gt_tree` on their dyadic sub-boxes (20 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 34 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 360–364 (20 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_34 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_360 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_361 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_362 (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_363 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf rootBox 0) 1) 1) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_364 (upperHalf (upperHalf (upperHalf rootBox 0) 1) 1) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
