-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01_s0
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s0
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T22:15:45.171977+00:00
-- url     : https://prove2.me/theorems/a20941a2-b2db-40f8-914a-f514d01525ab
-- title:
--   Fiber-gate certificate, part 1, sub-part 0
-- statement:
--   Sub-part 0 of part 1 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_10` … `gtc_13` of `gt_tree` on their dyadic sub-boxes (9 leaf boxes), with the Taylor-model enclosure `GQ.enc`. Part 1 is the conjunction of its sub-parts (split to fit the verification time limit).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Sub-part 0 of part 1 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 10–13 (9 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_01_s0 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_10 (lowerHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_11 (upperHalf (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_12 (lowerHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_13 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 1) 2) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
