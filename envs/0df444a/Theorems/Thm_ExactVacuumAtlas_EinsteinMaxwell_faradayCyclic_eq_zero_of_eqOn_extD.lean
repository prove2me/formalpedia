-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_faradayCyclic_eq_zero_of_eqOn_extD
-- name    : ExactVacuumAtlas.EinsteinMaxwell.faradayCyclic_eq_zero_of_eqOn_extD
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:46:11.907796+00:00
-- url     : https://prove2.me/theorems/9275e1dc-45b4-470b-9205-269d5060202b
-- title:
--   dA is closed
-- statement:
--   dA is closed
--
--   On an open set where F = extD A with C^∞ A, every H_abc(F) = 0 (symmetry of second partial derivatives).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** F = dA 时 H = 0。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Certificate.lean#L123-L137; SHA-256 96047b8402974e172119af74b269b2642fe03c56261d6475022bc193053e6c50. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
open scoped ContDiff

theorem ExactVacuumAtlas.EinsteinMaxwell.faradayCyclic_eq_zero_of_eqOn_extD {n : ℕ} {A : CoVec n} {F : TwoForm n} {U : Set (Pt n)}
    (hU : IsOpen U) (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U) (hF : ∀ i j, Set.EqOn (F i j) (extD A i j) U)
    {x : Pt n} (hx : x ∈ U) (a b c : Fin n) : faradayCyclic F a b c x = 0 := by sorry
