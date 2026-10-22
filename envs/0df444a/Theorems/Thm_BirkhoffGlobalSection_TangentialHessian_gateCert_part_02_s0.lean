-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_02_s0
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_02_s0
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T22:16:00.244986+00:00
-- url     : https://prove2.me/theorems/4c5388f5-dff1-44ed-8ffb-8464771a532a
-- title:
--   Fiber-gate certificate, part 2, sub-part 0
-- statement:
--   Sub-part 0 of part 2 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_21` … `gtc_25` of `gt_tree` on their dyadic sub-boxes (11 leaf boxes), with the Taylor-model enclosure `GQ.enc`. Part 2 is the conjunction of its sub-parts (split to fit the verification time limit).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Sub-part 0 of part 2 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 21–25 (11 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_02_s0 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_21 (lowerHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_22 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_23 (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_24 (lowerHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_25 (lowerHalf (upperHalf (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 1) 0) 2) 2) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
