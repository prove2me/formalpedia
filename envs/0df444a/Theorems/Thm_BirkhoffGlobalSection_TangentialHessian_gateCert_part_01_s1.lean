-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01_s1
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s1
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T22:15:48.850649+00:00
-- url     : https://prove2.me/theorems/1ef0c362-0622-4496-8363-cdb839603cdb
-- title:
--   Fiber-gate certificate, part 1, sub-part 1
-- statement:
--   Sub-part 1 of part 1 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_14` … `gtc_17` of `gt_tree` on their dyadic sub-boxes (13 leaf boxes), with the Taylor-model enclosure `GQ.enc`. Part 1 is the conjunction of its sub-parts (split to fit the verification time limit).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Sub-part 1 of part 1 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 14–17 (13 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_01_s1 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_14 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_15 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_16 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_17 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
