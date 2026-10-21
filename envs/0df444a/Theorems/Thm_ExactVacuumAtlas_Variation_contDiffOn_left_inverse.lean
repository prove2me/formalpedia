-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_contDiffOn_left_inverse
-- name    : ExactVacuumAtlas.Variation.contDiffOn_left_inverse
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:23.148267+00:00
-- url     : https://prove2.me/theorems/2a9d6a16-1aad-4d8e-aa91-ed5243f0acb0
-- title:
--   C^∞ of a true inverse
-- statement:
--   C^∞ of a true inverse
--
--   If A is entrywise C^∞ on s and B · A = 1 on s, then B is entrywise C^∞ on s.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 真逆的 C^∞。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Joint.lean#L171-L180; SHA-256 4b63c47f27fd80bedab505cf38c5c13014839c88f3159852417904171ca49a55. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ExactVacuumAtlas.Variation.contDiffOn_left_inverse {s : Set E} {A B : E → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun p => A p a b) s) (hBA : ∀ p ∈ s, B p * A p = 1) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun p => B p a b) s := by sorry
