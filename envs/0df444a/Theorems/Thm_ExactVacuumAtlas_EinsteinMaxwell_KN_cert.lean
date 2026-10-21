-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_cert
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.cert
-- status  : Open
-- author  : @He Wang
-- created : 2026-10-21T01:49:10.541921+00:00
-- url     : https://prove2.me/theorems/d4f531bc-62c3-4e24-85d7-ee2236d5b7bf
-- title:
--   Kerr–Newman in Boyer–Lindquist coordinates: full certificate on the exterior domain
-- statement:
--   Kerr–Newman in Boyer–Lindquist coordinates: full certificate on the exterior domain
--
--   For M > 0 and all real a, Q. Coordinates (t, r, θ, φ) = (x⁰, x¹, x², x³); Σ = r² + a² cos²θ, Δ = r² − 2Mr + a² + Q². Metric gKN: g_tt = −(Δ − a² sin²θ)/Σ, g_tφ = g_φt = −a(2Mr − Q²) sin²θ/Σ, g_rr = Σ/Δ, g_θθ = Σ, g_φφ = sin²θ((r² + a²)² − a²Δ sin²θ)/Σ; giKN its certified inverse; field faradayKN a Q = dA with A = −(Qr/Σ)(dt − a sin²θ dφ) (faraday_eq_extD). Statement: EinsteinMaxwellCertificate (gKN M a Q) (giKN M a Q) (faradayKN a Q) (domKN M a Q), domKN = {rPlus < r, 0 < θ < π}, rPlus = M + √(M² − a² − Q²) with Real.sqrt (= 0 for a negative argument).
--
--   **Scope.** Every M > 0, every real a, Q (a = 0, Q = 0 allowed). Physical black-hole exterior interpretation adopted in this release: a² + Q² < M² (rPlus = outer horizon radius). At a² + Q² = M², rPlus = M is likewise a (double) root of Δ = (r − M)². For a² + Q² > M² the threshold rPlus = M is not a root of Δ; the certificate then states exactly the printed regular-coordinate domain. No horizon or global theorem.
--
--   **中文摘要** KN（BL 坐标）对 M>0 与任意实 a、Q，在 domKN = {r₊ < r, 0<θ<π} 上的完整 Einstein–Maxwell 证书。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L238-L242; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.cert (M a Q : ℝ) (hM : 0 < M) :
    EinsteinMaxwellCertificate (gKN M a Q) (giKN M a Q) (faradayKN a Q) (domKN M a Q) := by sorry
