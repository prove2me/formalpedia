-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_certStdRN
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.certStdRN
-- status  : Open
-- author  : @He Wang
-- created : 2026-10-21T01:49:11.424614+00:00
-- url     : https://prove2.me/theorems/f307c8ab-b4d0-4f25-9882-6d52f78a9730
-- title:
--   KN at a = 0 gives the Reissner–Nordström certificate in standard coordinates
-- statement:
--   KN at a = 0 gives the Reissner–Nordström certificate in standard coordinates
--
--   For M > 0 and real Q: EinsteinMaxwellCertificate (gStdRN M Q) (giStdRN M Q) (faradayStdRN Q) (domStdRN M Q), with coordinates (t, r, θ, φ), gStdRN = diag(−f, 1/f, r², r² sin²θ), f = 1 − 2M/r + Q²/r², giStdRN = diag(−1/f, f, r⁻², (r² sin²θ)⁻¹), F_rt = Q/r² = −F_tr, domStdRN = {M + √(M² − Q²) < r, 0 < θ < π}. Obtained by specialising the KN certificate to a = 0.
--
--   **Scope.** Parameter substitution a = 0 (equality of data on domKN M 0 Q = domStdRN M Q). Not the ingoing-EF chart of milestone 1; no EF ↔ standard coordinate relation is claimed.
--
--   **中文摘要** a = 0 特化：标准坐标 RN 的完整证书；这不是 IV-01 的 EF 坐标，也不声称 EF↔标准坐标映射。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Special.lean#L1633-L1641; SHA-256 8ec8234538cef3eac7f462a57128cdaa80597af52a2efef1190c8df8425ba5a3. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_RNStd_Defs
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.KN
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.certStdRN (M Q : ℝ) (hM : 0 < M) :
    EinsteinMaxwellCertificate (RNStd.gStdRN M Q) (RNStd.giStdRN M Q) (RNStd.faradayStdRN Q)
      (RNStd.domStdRN M Q) := by sorry
