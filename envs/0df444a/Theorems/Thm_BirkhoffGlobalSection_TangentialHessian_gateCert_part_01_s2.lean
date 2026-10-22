-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01_s2
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_01_s2
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T22:15:56.781987+00:00
-- url     : https://prove2.me/theorems/3e877920-6ae7-4e55-817b-518a4f465b89
-- title:
--   Fiber-gate certificate, part 1, sub-part 2
-- statement:
--   Sub-part 2 of part 1 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_18` … `gtc_20` of `gt_tree` on their dyadic sub-boxes (6 leaf boxes), with the Taylor-model enclosure `GQ.enc`. Part 1 is the conjunction of its sub-parts (split to fit the verification time limit).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Sub-part 2 of part 1 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 18–20 (6 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_01_s2 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_18 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_19 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_20 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 0) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
