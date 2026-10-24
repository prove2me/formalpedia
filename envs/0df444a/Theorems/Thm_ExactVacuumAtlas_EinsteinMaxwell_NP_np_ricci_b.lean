-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_ricci_b
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_ricci_b
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:07.361999+00:00
-- url     : https://prove2.me/theorems/3ea6a3f5-bd99-4c1b-868b-176d6e1d135f
-- title:
--   NP Ricci identity (4.2b)
-- statement:
--   NP Ricci identity (4.2b)
--
--   Any null frame: Dσ − δκ = σ(ρ + ρ̄ + 3ε − ε̄) − κ(τ − π̄ + ᾱ + 3β) + Ψ₀. Source of III's res1c. Here barred spin-coefficient symbols denote the B-suffixed, m↔m̄ index-swapped quantities in the formal statement; numerical complex conjugacy is not assumed for a general complex frame.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** NP Ricci 恒等式 (4.2b)；res1c 的来源。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPRicci.lean#L127-L140; SHA-256 ac60d8d4c03ef192711b765ff96839ab1c7b0d06979f363abf6f01f165ba36cf. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameNull
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_ricci_b (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) :
    fdir E 0 (omL g gi E Θ 0 2 2) x - fdir E 2 (omL g gi E Θ 0 0 2) x
      = npSigma g gi E Θ x * (npRho g gi E Θ x + npRhoB g gi E Θ x + 3 * npEps g gi E Θ x - npEpsB g gi E Θ x)
        - npKappa g gi E Θ x * (npTau g gi E Θ x - npPiB g gi E Θ x + npAlphaB g gi E Θ x + 3 * npBeta g gi E Θ x)
        + psi0 g gi E x := by sorry
