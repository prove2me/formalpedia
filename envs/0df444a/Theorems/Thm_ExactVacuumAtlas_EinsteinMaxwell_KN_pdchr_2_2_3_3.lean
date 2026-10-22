-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_pdchr_2_2_3_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.pdchr_2_2_3_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T11:00:05.482972+00:00
-- url     : https://prove2.me/theorems/94168fb7-e813-483b-93bc-80b90a41dc89
-- title:
--   KN Christoffel derivative ∂_2 Γ^2_{33}
-- statement:
--   KN Christoffel derivative ∂_2 Γ^2_{33}
--
--   For every real M, a, Q and x ∈ domReg M a Q = {Σ ≠ 0, Δ ≠ 0, sin θ ≠ 0}: closed form of the coordinate derivative pd 2 (christoffel (gKN M a Q) (giKN M a Q) 2 3 3) x, i.e. ∂_2 Γ^2_{33} of the Kerr–Newman Boyer–Lindquist metric, as the displayed polynomial in M, a, Q, r = x¹, sin θ, cos θ and the atom Ui = 1/Σ. It is one entry of the generated pd Γ table used by the Ricci component R_33.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement (every real M, a, Q; x ∈ domReg M a Q).
--
--   **中文摘要** KN 的 Christoffel 符号偏导 ∂_2 Γ^2_{33} 在 domReg 上的闭式（R_33 计算所需的表项）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/PdChr.lean#L888-L894; SHA-256 2d40cb2596b5910d1a6d021bb4800ba97c43184bd967d598d52290a40191c57e. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.pdchr_2_2_3_3 (x : Pt 4) (hx : x ∈ domReg M a Q) :
    pd 2 (christoffel (gKN M a Q) (giKN M a Q) 2 3 3) x = ((12:ℝ) * M * a^6) * (x 1) * sin (x 2) ^ 6 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-24:ℝ) * M * a^6) * (x 1) * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-24:ℝ) * M * a^4) * (x 1) ^ 3 * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-2:ℝ) * M * a^4) * (x 1) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((10:ℝ) * M * a^4) * (x 1) * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((4:ℝ) * M * a^4) * (x 1) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-12:ℝ) * M * a^4) * (x 1) * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((4:ℝ) * M * a^2) * (x 1) ^ 3 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((-12:ℝ) * M * a^2) * (x 1) ^ 3 * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-6:ℝ) * a^8) * sin (x 2) ^ 6 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((12:ℝ) * a^8) * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-6:ℝ) * a^8) * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-6:ℝ) * a^6 * Q^2) * sin (x 2) ^ 6 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((12:ℝ) * a^6 * Q^2) * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-6:ℝ) * a^6) * (x 1) ^ 2 * sin (x 2) ^ 6 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((24:ℝ) * a^6) * (x 1) ^ 2 * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-18:ℝ) * a^6) * (x 1) ^ 2 * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((1:ℝ) * a^6) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((-5:ℝ) * a^6) * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-2:ℝ) * a^6) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^6) * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((1:ℝ) * a^6) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-1:ℝ) * a^6) * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((12:ℝ) * a^4 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((1:ℝ) * a^4 * Q^2) * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((-5:ℝ) * a^4 * Q^2) * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-2:ℝ) * a^4 * Q^2) * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^4 * Q^2) * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((12:ℝ) * a^4) * (x 1) ^ 4 * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-18:ℝ) * a^4) * (x 1) ^ 4 * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((1:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 6 * Ui a (x 1) (x 2) ^ 3 + ((-5:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-4:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((12:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((3:ℝ) * a^4) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-3:ℝ) * a^4) * (x 1) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-2:ℝ) * a^2 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^2 * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-6:ℝ) * a^2) * (x 1) ^ 6 * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 4 + ((-2:ℝ) * a^2) * (x 1) ^ 4 * sin (x 2) ^ 4 * Ui a (x 1) (x 2) ^ 3 + ((6:ℝ) * a^2) * (x 1) ^ 4 * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((3:ℝ) * a^2) * (x 1) ^ 4 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-3:ℝ) * a^2) * (x 1) ^ 4 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((1:ℝ)) * (x 1) ^ 6 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-1:ℝ)) * (x 1) ^ 6 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 := by sorry
