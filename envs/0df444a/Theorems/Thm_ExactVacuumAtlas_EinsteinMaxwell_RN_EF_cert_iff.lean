-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_EF_cert_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.EF.cert_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:47.541085+00:00
-- url     : https://prove2.me/theorems/ce792cb8-ab84-4f55-a2ea-75ad1f2ec9cb
-- title:
--   Reissner–Nordström in ingoing Eddington–Finkelstein coordinates: certificate iff b = Q²
-- statement:
--   Reissner–Nordström in ingoing Eddington–Finkelstein coordinates: certificate iff b = Q²
--
--   For all real M, Q, b. Coordinates (v, r, θ, φ) = (x⁰, x¹, x², x³). Ansatz gRN M b: g_vv = −f_b, g_vr = g_rv = 1, g_θθ = r², g_φφ = r² sin²θ, other components 0, with f_b = 1 − 2M/r + b/r²; candidate inverse giRN M b (g^{vr} = g^{rv} = 1, g^{rr} = f_b, g^{θθ} = r⁻², g^{φφ} = (r² sin²θ)⁻¹); field faradayRN Q: F_vr = −Q/r², F_rv = Q/r². Statement: EinsteinMaxwellCertificate (gRN M b) (giRN M b) (faradayRN Q) domRN ↔ b = Q², where domRN = {r > 0, 0 < θ < π}. The parameter b is independent of Q; the equivalence holds within this fixed ansatz only.
--
--   **Scope.** Every real M, Q, b (no sign condition on M). Not a uniqueness, Birkhoff or classification statement; only the fixed ansatz.
--
--   **中文摘要** RN 入射 EF 固定拟设内：完整 Einstein–Maxwell 证书在 domRN 上成立 ⟺ b = Q²（b 与 Q 独立，M、Q、b 为任意实数）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/EFCert.lean#L204-L211; SHA-256 357f1c6dcc9d4b1de6bc91d8180a4c7e5b75316199ee7ef426a62e658987ab64. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Frame
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.RN
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.RN
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.EF.cert_iff (M Q b : ℝ) :
    EinsteinMaxwellCertificate (gRN M b) (giRN M b) (faradayRN Q) domRN ↔ b = Q ^ 2 := by sorry
