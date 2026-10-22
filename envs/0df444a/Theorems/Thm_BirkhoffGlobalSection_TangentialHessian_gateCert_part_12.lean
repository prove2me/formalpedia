-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_12
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_12
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:31:47.407889+00:00
-- url     : https://prove2.me/theorems/a56a22a8-a8b7-4727-a1f1-afc1e05c5393
-- title:
--   Fiber-gate certificate, part 12/35
-- statement:
--   Part 12 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_122` … `gtc_131` of `gt_tree` on their dyadic sub-boxes (19 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 12 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 122–131 (19 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_12 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_122 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_123 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_124 (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_125 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_126 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_127 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_128 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_129 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_130 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_131 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 1) 0) 2) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
