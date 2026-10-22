-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_01
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:31:04.313369+00:00
-- url     : https://prove2.me/theorems/e2a835b5-1dd7-48cc-8451-cfac3ce2e18f
-- title:
--   Fiber-gate certificate, part 1/35
-- statement:
--   Part 1 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_10` … `gtc_20` of `gt_tree` on their dyadic sub-boxes (28 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 1 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 10–20 (28 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_01 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_10 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_11 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_12 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_13 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_14 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_15 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_16 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_17 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_18 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_19 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_20 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
