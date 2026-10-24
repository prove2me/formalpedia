-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_v01_frame
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.v01_frame
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:26:47.340626+00:00
-- url     : https://prove2.me/theorems/e540d006-26b2-4c62-bfd9-07ec0bf8f758
-- title:
--   Kerr–Newman Kinnersley null frame: Gram matrix, duality, inverse metric and reconstruction
-- statement:
--   Kerr–Newman Kinnersley null frame: Gram matrix, duality, inverse metric and reconstruction
--
--   For every real M, a, Q: domReg M a Q (Σ ≠ 0, Δ ≠ 0, sin θ ≠ 0) is open and nonempty; every component of the Kinnersley frame knFrame (l = ((r²+a²)/Δ, 1, 0, a/Δ), n = (r²+a², −Δ, 0, a)/(2Σ), m = (ia sin θ, 0, 1, i/sin θ)/(√2 q), m̄ = conj m) is C^∞ on domReg; and at every x ∈ domReg: Tᵀ g T = etaNull (bilinear Gram matrix with g(l,n) = g(n,l) = −1 and g(m,m̄) = g(m̄,m) = 1; all remaining pairings are 0), m̄ = conj m componentwise, knDual · T = 1 and T · knDual = 1, T etaNull Tᵀ = giKN, and knDualᵀ etaNull knDual = gKN.
--
--   **Scope.** Every real M, a, Q (a = 0 and Q = 0 allowed); points of domReg only.
--
--   **中文摘要** KN 的 Kinnersley 零标架：domReg 开且非空、分量 C^∞、双线性 Gram 矩阵为 etaNull、m̄=conj m、对偶余标架为真逆、逆度规与度规的标架重建。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V01.lean#L15-L28; SHA-256 163c0780f59c9198d1097ef71bf5f7b6a5671f5ab3e49027f671fc9cbbb4a34a. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_ModeOperators
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Real
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.KN (gKN giKN faradayKN domReg domKN)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.v01_frame (M a Q : ℝ) :
    IsOpen (domReg M a Q) ∧ (domReg M a Q).Nonempty ∧
    (∀ A μ : Fin 4, ContDiffOn ℝ ∞ (fun x => knFrame M a Q x A μ) (domReg M a Q)) ∧
    ∀ x ∈ domReg M a Q,
      (knT M a Q x)ᵀ * cmat (gKN M a Q) x * knT M a Q x = etaNull ∧
      (∀ μ, knMbar a x μ = conj (knM a x μ)) ∧
      knDual M a Q x * knT M a Q x = 1 ∧ knT M a Q x * knDual M a Q x = 1 ∧
      knT M a Q x * etaNull * (knT M a Q x)ᵀ = cmat (giKN M a Q) x ∧
      (knDual M a Q x)ᵀ * etaNull * knDual M a Q x = cmat (gKN M a Q) x := by sorry
