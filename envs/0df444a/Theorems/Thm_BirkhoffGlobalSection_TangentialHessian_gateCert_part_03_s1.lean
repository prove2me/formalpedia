-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_03_s1
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_03_s1
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T22:16:12.617993+00:00
-- url     : https://prove2.me/theorems/4bddd5a0-621b-4d52-b322-506729f4a6fa
-- title:
--   Fiber-gate certificate, part 3, sub-part 1
-- statement:
--   Sub-part 1 of part 3 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_37` … `gtc_41` of `gt_tree` on their dyadic sub-boxes (12 leaf boxes), with the Taylor-model enclosure `GQ.enc`. Part 3 is the conjunction of its sub-parts (split to fit the verification time limit).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Sub-part 1 of part 3 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 37–41 (12 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_03_s1 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_37 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_38 (lowerHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_39 (upperHalf (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_40 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_41 (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 2) 0) 2) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
