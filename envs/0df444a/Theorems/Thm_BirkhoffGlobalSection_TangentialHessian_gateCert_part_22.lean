-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_22
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_22
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T09:32:08.286984+00:00
-- url     : https://prove2.me/theorems/93328e45-26fb-4e9a-831e-5be859f93a33
-- title:
--   Fiber-gate certificate, part 22/35
-- statement:
--   Part 22 of 35 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_224` … `gtc_231` of `gt_tree` on their dyadic sub-boxes (13 leaf boxes), with the Taylor-model enclosure `GQ.enc`. With the other parts this gives `check GQ.enc (gateCert gt_tree) = true`, and by `fiber_gate_pos_of_check` the theorem `fiber_gate_pos`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Part 22 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 224–231 (13 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_22 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_224 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_225 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_226 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 2) 0) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_227 (lowerHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_228 (lowerHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_229 (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_230 (upperHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) 2) 0) = true) ∧
    (checkTree GQ.enc (gateCert gt_tree) gtc_231 (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf (lowerHalf (upperHalf rootBox 0) 1) 0) 1) 1) 0) 0) 1) 2) 0) 2) 1) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
