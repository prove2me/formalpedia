-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_05
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_05
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:31:24.18169+00:00
-- url     : https://prove2.me/theorems/d555f708-2a06-46f5-9589-1f13e1067c52
-- title:
--   Fiber-gate certificate, part 5/35
-- statement:
--   Part 5 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_56` … `gtc_66` of `gt_tree` on their dyadic sub-boxes (33 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 5 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 56–66 (33 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_05 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_56 (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_57 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_58 (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_59 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_60 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_61 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_62 (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_63 (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_64 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_65 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_66 (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 2) 0) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
