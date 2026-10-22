-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_00_s2
-- name    : BirkhoffGlobalSection.TangentialHessian.gateCert_part_00_s2
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-01T18:53:18.258341+00:00
-- url     : https://prove2.me/theorems/99f58247-7a4a-4c4a-87f7-e6cc2453d787
-- title:
--   Fiber-gate certificate, part 0, sub-part 2
-- statement:
--   Sub-part 2 of part 0 of the kernel-checked certificate for the fiber gate inequality `fiber_gate_pos`: the verified checker accepts the subtrees `gtc_9` … `gtc_9` of `gt_tree` on their dyadic sub-boxes (3 leaf boxes), with the Taylor-model enclosure `GQ.enc`. Part 0 is the conjunction of its sub-parts (split to fit the verification time limit).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM
  BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

namespace BirkhoffGlobalSection.TangentialHessian

/-- Sub-part 2 of part 0 of 35 of the fiber-gate certificate `gateCert gt_tree`: the verified checker accepts chunks 9–9 (3 boxes) of the branch-and-bound tree. -/
theorem gateCert_part_00_s2 :
    (checkTree GQ.enc (gateCert gt_tree) gtc_9 (upperHalf (lowerHalf (upperHalf (upperHalf (lowerHalf (lowerHalf (lowerHalf rootBox 0) 1) 1) 0) 0) 2) 2) = true) := by sorry

end BirkhoffGlobalSection.TangentialHessian
