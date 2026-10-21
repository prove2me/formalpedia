-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_contDiffOn_adjugate_of
-- name    : ExactVacuumAtlas.Variation.contDiffOn_adjugate_of
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:23.787472+00:00
-- url     : https://prove2.me/theorems/c43e2ec0-9421-41cc-9ed1-3b7e107dfc09
-- title:
--   C^∞ of the adjugate
-- statement:
--   C^∞ of the adjugate
--
--   Entrywise C^∞ of a matrix field implies entrywise C^∞ of its adjugate (any normed real domain).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 伴随矩阵的 C^∞。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Joint.lean#L159-L169; SHA-256 4b63c47f27fd80bedab505cf38c5c13014839c88f3159852417904171ca49a55. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ExactVacuumAtlas.Variation.contDiffOn_adjugate_of {s : Set E} {A : E → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun p => A p a b) s) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun p => (A p).adjugate a b) s := by sorry
