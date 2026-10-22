-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_04_s1
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_04_s1
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T22:16:23.692577+00:00
-- url     : https://prove2.me/theorems/68443652-7829-4ceb-ae8e-83fab41c6a3b
-- title:
--   Fiber-gate certificate, part 4, sub-part 1
-- statement:
--   Sub-part 1 of part 4 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_50` … `gtc_55` of `gt_tree` on their dyadic sub-boxes (14 leaf boxes), with the Taylor-model enclosure `GQ.enc`. Part 4 is the conjunction of its sub-parts (split to fit the verification time limit).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Sub-part 1 of part 4 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 50–55 (14 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_04_s1 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_50 (upperHalf (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_51 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_52 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_53 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_54 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_55 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 1) 0) 2) 0) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
