-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_ricci_law
-- name    : ExactVacuumAtlas.Release02.ricci_law
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:31:54.30698+00:00
-- url     : https://prove2.me/theorems/9346580f-4aa1-41b4-923a-7ff7c2fc6b04
-- title:
--   Transformation law of the coordinate Ricci tensor under a smooth coordinate change (any dimension n)
-- statement:
--   Let n be any natural number, U, V ⊆ ℝⁿ, Φ : ℝⁿ → ℝⁿ, J, K matrix-valued maps and g, ĝ, h, ĥ coordinate metrics. Assume CoordChange U V Φ J K and MetricData h ĥ V, and the two pull-back identities g(y) = J(y)ᵀ h(Φ y) J(y) and ĝ(y) = K(y) ĥ(Φ y) K(y)ᵀ for every y ∈ U. Then for every y ∈ U and all indices i, j: Ric(g,ĝ)_{ij}(y) = Σ_a Σ_b J(y)_{ai} J(y)_{bj} Ric(h,ĥ)_{ab}(Φ y). CoordChange U V Φ J K (bundle Atlas_Transport_Connection, new) is the conjunction of six obligations: U open; V open; Φ C^∞ on U; Φ maps U into V; J(y)_{ki} is the genuine slice derivative of Φ_k in the i-th coordinate at every y ∈ U; and J(y)·K(y) = I for every y ∈ U. MetricData h ĥ V (same bundle) is the conjunction of five obligations: V open; h symmetric on V; ĥ(x)·h(x) = I on V; h C^∞ on V; ĥ C^∞ on V — no curvature condition. Ric is the registered coordinate Ricci tensor of release I (ricciOf, bundle Atlas_Core_Basic), not redefined.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/TransportMilestone.lean#L33-L40; SHA-256 e066de778216dc552a43e41e7967661796a78d9fd40c374cb701b56fdf9c42ae. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Controls_CylinderTables
import Definitions.Def_Atlas_Controls_Shear
import Definitions.Def_Atlas_Controls_ShearTables
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Isotropic_CartChart
import Definitions.Def_Atlas_Isotropic_CartCover
import Definitions.Def_Atlas_Isotropic_CartMaps
import Definitions.Def_Atlas_Isotropic_Defs
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGCertParts
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Matrix
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild ExactVacuumAtlas.Controls

theorem ExactVacuumAtlas.Release02.ricci_law {n : ℕ} {U V : Set (Pt n)} {Φ : Pt n → Pt n}
    {J K : Pt n → Matrix (Fin n) (Fin n) ℝ} {g gi h hi : Metric n}
    (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ) :
    ∀ y ∈ U, ∀ i j, ricciOf g gi i j y = ∑ a, ∑ b, J y a i * J y b j * ricciOf h hi a b (Φ y) := by sorry
