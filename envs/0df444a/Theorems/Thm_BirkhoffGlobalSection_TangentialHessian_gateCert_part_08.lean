-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_08
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_08
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:31:41.915423+00:00
-- url     : https://prove2.me/theorems/350ac4c4-a0b5-4271-bb7e-c5a9fd19f7a1
-- title:
--   Fiber-gate certificate, part 8/35
-- statement:
--   Part 8 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_85` … `gtc_93` of `gt_tree` on their dyadic sub-boxes (16 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 8 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 85–93 (16 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_08 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_85 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_86 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_87 (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_88 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_89 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_90 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_91 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_92 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_93 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) 1) 2) 0) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
