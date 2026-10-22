-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_pdchr_1_1_3_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.pdchr_1_1_3_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T11:00:21.116623+00:00
-- url     : https://prove2.me/theorems/a7c33c73-6b3e-4896-8ce2-ffef7d7ccc2e
-- title:
--   KN Christoffel derivative ∂_1 Γ^1_{33}
-- statement:
--   KN Christoffel derivative ∂_1 Γ^1_{33}
--
--   For every real M, a, Q and x ∈ domReg M a Q = {Σ ≠ 0, Δ ≠ 0, sin θ ≠ 0}: closed form of the coordinate derivative pd 1 (christoffel (gKN M a Q) (giKN M a Q) 1 3 3) x, i.e. ∂_1 Γ^1_{33} of the Kerr–Newman Boyer–Lindquist metric, as the displayed polynomial in M, a, Q, r = x¹, sin θ, cos θ and the atom Ui = 1/Σ. It is one entry of the generated pd Γ table used by the Ricci component R_33.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement (every real M, a, Q; x ∈ domReg M a Q).
--
--   **中文摘要** KN 的 Christoffel 符号偏导 ∂_1 Γ^1_{33} 在 domReg 上的闭式（R_33 计算所需的表项）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/PdChr.lean#L448-L454; SHA-256 2d40cb2596b5910d1a6d021bb4800ba97c43184bd967d598d52290a40191c57e. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_InAtoms
open Real
open ExactVacuumAtlas
open scoped ContDiff
open ExactVacuumAtlas.Kerr.In (Ui Wi)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.KN
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M a Q : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.pdchr_1_1_3_3 (x : Pt 4) (hx : x ∈ domReg M a Q) :
    pd 1 (christoffel (gKN M a Q) (giKN M a Q) 1 3 3) x = ((12:ℝ) * M^2 * a^4) * (x 1) ^ 2 * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 4 + ((-12:ℝ) * M^2 * a^4) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((-2:ℝ) * M^2 * a^4) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((2:ℝ) * M^2 * a^4) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((12:ℝ) * M^2 * a^2) * (x 1) ^ 4 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((-6:ℝ) * M^2 * a^2) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-6:ℝ) * M * a^6) * (x 1) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 4 + ((6:ℝ) * M * a^6) * (x 1) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((-6:ℝ) * M * a^4 * Q^2) * (x 1) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 4 + ((6:ℝ) * M * a^4 * Q^2) * (x 1) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((-18:ℝ) * M * a^4) * (x 1) ^ 3 * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 4 + ((24:ℝ) * M * a^4) * (x 1) ^ 3 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((-12:ℝ) * M * a^4) * (x 1) ^ 3 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((6:ℝ) * M * a^4) * (x 1) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((-8:ℝ) * M * a^4) * (x 1) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((4:ℝ) * M * a^4) * (x 1) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-18:ℝ) * M * a^2 * Q^2) * (x 1) ^ 3 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((6:ℝ) * M * a^2 * Q^2) * (x 1) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((18:ℝ) * M * a^2) * (x 1) ^ 5 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((-24:ℝ) * M * a^2) * (x 1) ^ 5 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-12:ℝ) * M * a^2) * (x 1) ^ 3 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((16:ℝ) * M * a^2) * (x 1) ^ 3 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-12:ℝ) * M) * (x 1) ^ 7 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((12:ℝ) * M) * (x 1) ^ 5 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^6) * (x 1) ^ 2 * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 4 + ((-12:ℝ) * a^6) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((6:ℝ) * a^6) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-1:ℝ) * a^6) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((2:ℝ) * a^6) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-1:ℝ) * a^6) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^4 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 4 + ((-6:ℝ) * a^4 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((6:ℝ) * a^4 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-1:ℝ) * a^4 * Q^2) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((1:ℝ) * a^4 * Q^2) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-1:ℝ) * a^4 * Q^2) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^4) * (x 1) ^ 4 * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 4 + ((-24:ℝ) * a^4) * (x 1) ^ 4 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((18:ℝ) * a^4) * (x 1) ^ 4 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-3:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((12:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-9:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^2 * Q^4) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((-1:ℝ) * a^2 * Q^4) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-6:ℝ) * a^2 * Q^2) * (x 1) ^ 4 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((12:ℝ) * a^2 * Q^2) * (x 1) ^ 4 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((3:ℝ) * a^2 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-6:ℝ) * a^2 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-12:ℝ) * a^2) * (x 1) ^ 6 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 4 + ((18:ℝ) * a^2) * (x 1) ^ 6 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((10:ℝ) * a^2) * (x 1) ^ 4 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-15:ℝ) * a^2) * (x 1) ^ 4 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * Q^2) * (x 1) ^ 6 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-5:ℝ) * Q^2) * (x 1) ^ 4 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ)) * (x 1) ^ 8 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-7:ℝ)) * (x 1) ^ 6 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 := by sorry
