-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_ricci_of
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_ricci_of
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:24.960967+00:00
-- url     : https://prove2.me/theorems/7820d9bc-c213-4ce2-a95f-71ac2f63786a
-- title:
--   Pointwise derivative of the Ricci expression
-- statement:
--   Pointwise derivative of the Ricci expression
--
--   Given ε-derivatives of Γ and of ∂Γ at y, the derivative of the Ricci expression is ricciLin Γ C.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Ricci 表达式的导数。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L63-L70; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
variable {g ginv : ℝ → Metric n} {F : ℝ → TwoForm n} {h : Metric n} {f : TwoForm n} {y : Pt n}

theorem ExactVacuumAtlas.Variation.hasDerivAt_ricci_of {Γ : ℝ → Fin n → Fin n → Fin n → Pt n → ℝ}
    {C : Fin n → Fin n → Fin n → Pt n → ℝ}
    (hΓ : ∀ a b c, HasDerivAt (fun ε => Γ ε a b c y) (C a b c y) 0)
    (hpΓ : ∀ i a b c, HasDerivAt (fun ε => pd i (Γ ε a b c) y) (pd i (C a b c) y) 0) (b d : Fin n) :
    HasDerivAt (fun ε => ricci (Γ ε) b d y) (ricciLin (Γ 0) C b d y) 0 := by sorry
